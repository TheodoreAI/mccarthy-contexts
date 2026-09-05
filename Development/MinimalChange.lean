/-
  Minimal change for relaxed transcendence contexts.

  Earlier results establish that the transcendence schema is categorical over the
  base (a context obeying it is uniquely determined), that any genuine
  relaxation refutes the schema, and that dropping even one instance destroys
  uniqueness.  So a relaxed tower is underdetermined, and a *logic* of relaxing
  contexts must say which of the surviving contexts is intended.

  The obvious candidate -- and McCarthy's own instinct, since circumscription is
  his invention -- is to prefer contexts that change as little as possible.
  This file measures exactly how much freedom relaxation leaves, and shows that
  the minimal-change answer is degenerate.

  Writing `Δ(N)` for the set of assumptions at which `N` departs from the
  context below, and `Mod(v,A)` for the contexts extending `v` that obey the
  schema off `A`:

    1. `delta_subset`        `N ∈ Mod(v,A) → Δ(N) ⊆ A`
    2. `mod_iff`             `Mod(v,A) = {N extending v : Δ(N) ⊆ A}`
    3. `delta_injOn`,        `Δ` is a bijection `Mod(v,A) → 𝒫(A)`
       `delta_surjOn`
    4. `copy_mem`, `delta_copy`, `eq_copy_of_delta_empty`, `copy_minimal`
                             the copy context is the unique `Δ = ∅` model,
                             hence the ⊆-minimum, for *every* `A`
    5. `forced_unique`       `{N ∈ Mod(v,A) : Δ(N) = A}` is a singleton

  Statements 3-5 are the point.  By 3, relaxing `k` assumptions leaves exactly
  `2^k` contexts and the relaxed schema constrains nothing beyond confining
  change to `A`.  By 4, minimising change returns the unrelaxed tower for every
  `A`, so circumscribing the abnormality recovers precisely the case McCarthy
  calls pointless.  By 5, *specifying* the change set determines the context
  uniquely.

  The moral: the content of a logic of relaxing contexts cannot come from a
  preference order over models -- it must come from saying which assumptions are
  dropped.
-/

import Definitions.Def_TranscendenceTowerRelaxation
import Mathlib.Data.Set.Basic

set_option autoImplicit false

open TranscendenceTower TranscendenceTower.Relaxation

namespace TranscendenceTower.MinimalChange

/-! ## Helpers -/

theorem eval_map' {A B : Type} (f : A → B) (w : B → Bool) (p : Form A) :
    Form.eval w (Form.map f p) = Form.eval (fun x => w (f x)) p := by
  induction p with
  | atom x => rfl
  | neg p ih => simp [Form.map, Form.eval, ih]
  | conj p q ihp ihq => simp [Form.map, Form.eval, ihp, ihq]
  | disj p q ihp ihq => simp [Form.map, Form.eval, ihp, ihq]
  | impl p q ihp ihq => simp [Form.map, Form.eval, ihp, ihq]

theorem eval_iff' {A : Type} (w : A → Bool) (p q : Form A) :
    Form.eval w (Form.iff p q) = true ↔ Form.eval w p = Form.eval w q := by
  simp only [Form.iff, Form.eval]
  cases hp : Form.eval w p <;> cases hq : Form.eval w q <;> simp

theorem eval_lift_of_extends {v : Atom 0 → Bool} {N : Atom 1 → Bool}
    (h : ExtendsBase v N) (p : Lang 0) :
    Form.eval N (lift p) = Form.eval v p := by
  have h1 : Form.eval N (lift p) = Form.eval (fun x => N (Sum.inl x)) p :=
    eval_map' (Sum.inl : Atom 0 → Atom 1) N p
  have h2 : (fun x => N (Sum.inl x)) = v := funext h
  rw [h1, h2]

/-- Satisfying the schema at `p` is exactly agreeing with the base at `p`. -/
theorem schema_iff {v : Atom 0 → Bool} {N : Atom 1 → Bool} (hext : ExtendsBase v N)
    (p : Lang 0) :
    Form.eval N (schema p) = true ↔ N (Sum.inr p) = Form.eval v p := by
  rw [show schema p = Form.iff (ist p) (lift p) from rfl, eval_iff' N (ist p) (lift p),
    eval_lift_of_extends hext p]
  exact Iff.rfl

/-- On `Bool`, differing from `c` means being `!c`. -/
theorem bool_ne_iff (b c : Bool) : b ≠ c ↔ b = !c := by
  cases b <;> cases c <;> simp

/-! ## Definitions -/

/-- The **change set** of a context: the assumptions at which it departs from
the context below. -/
def Delta (v : Atom 0 → Bool) (N : Atom 1 → Bool) : Set (Lang 0) :=
  {p | N (Sum.inr p) ≠ Form.eval v p}

/-- The **`A`-relaxed models**: contexts extending `v` that obey the
transcendence schema everywhere outside `A`. -/
def Mod (v : Atom 0 → Bool) (A : Set (Lang 0)) : Set (Atom 1 → Bool) :=
  {N | ExtendsBase v N ∧ ∀ p : Lang 0, p ∉ A → Form.eval N (schema p) = true}

/-- The canonical copy context: it carries every truth value upward unchanged. -/
def copy (v : Atom 0 → Bool) : Atom 1 → Bool := mk1 v (fun p => Form.eval v p)

theorem extendsBase_mk1 (v : Atom 0 → Bool) (g : Lang 0 → Bool) :
    ExtendsBase v (mk1 v g) := fun _ => rfl

/-! ## 1. Relaxation cannot spill outside `A` -/

theorem delta_subset {v : Atom 0 → Bool} {A : Set (Lang 0)} {N : Atom 1 → Bool}
    (h : N ∈ Mod v A) : Delta v N ⊆ A := by
  intro p hp
  by_contra hpA
  exact hp ((schema_iff h.1 p).mp (h.2 p hpA))

/-! ## 2. Being a relaxed model is exactly changing only within `A` -/

theorem mod_iff (v : Atom 0 → Bool) (A : Set (Lang 0)) :
    Mod v A = {N : Atom 1 → Bool | ExtendsBase v N ∧ Delta v N ⊆ A} := by
  ext N
  constructor
  · exact fun h => ⟨h.1, delta_subset h⟩
  · rintro ⟨hext, hsub⟩
    refine ⟨hext, fun p hpA => (schema_iff hext p).mpr ?_⟩
    by_contra hne
    exact hpA (hsub hne)

/-! ## 3. `Δ` parametrises the relaxed models by the subsets of `A` -/

/-- **Injectivity.**  Two relaxed models with the same change set are equal.
Because truth values are Boolean, knowing *where* a context departs from the
base determines *what* it says there. -/
theorem delta_injOn {v : Atom 0 → Bool} {A : Set (Lang 0)} {N₁ N₂ : Atom 1 → Bool}
    (h₁ : N₁ ∈ Mod v A) (h₂ : N₂ ∈ Mod v A) (hD : Delta v N₁ = Delta v N₂) :
    N₁ = N₂ := by
  funext x
  cases x with
  | inl a => rw [h₁.1 a, h₂.1 a]
  | inr p =>
      by_cases hp : p ∈ Delta v N₁
      · have hp2 : p ∈ Delta v N₂ := hD ▸ hp
        rw [(bool_ne_iff _ _).mp hp, (bool_ne_iff _ _).mp hp2]
      · have hp2 : p ∉ Delta v N₂ := fun hc => hp (hD ▸ hc)
        rw [not_not.mp hp, not_not.mp hp2]

/-- **Surjectivity.**  Every subset of `A` is realised as the change set of some
relaxed model.  So the relaxed schema imposes no constraint whatever beyond
confining change to `A`. -/
theorem delta_surjOn (v : Atom 0 → Bool) (A S : Set (Lang 0)) (hSA : S ⊆ A) :
    ∃ N : Atom 1 → Bool, N ∈ Mod v A ∧ Delta v N = S := by
  classical
  refine ⟨mk1 v (fun p => if p ∈ S then !(Form.eval v p) else Form.eval v p), ?_, ?_⟩
  · refine ⟨extendsBase_mk1 _ _, fun p hpA => (schema_iff (extendsBase_mk1 v _) p).mpr ?_⟩
    show (if p ∈ S then !(Form.eval v p) else Form.eval v p) = Form.eval v p
    rw [if_neg (fun hpS => hpA (hSA hpS))]
  · ext p
    show (if p ∈ S then !(Form.eval v p) else Form.eval v p) ≠ Form.eval v p ↔ p ∈ S
    by_cases hpS : p ∈ S
    · rw [if_pos hpS]
      simp [hpS]
    · rw [if_neg hpS]
      simp [hpS]

/-! ## 4. Minimal change collapses to the unrelaxed tower -/

theorem copy_mem (v : Atom 0 → Bool) (A : Set (Lang 0)) : copy v ∈ Mod v A :=
  ⟨extendsBase_mk1 _ _, fun p _ => (schema_iff (extendsBase_mk1 v _) p).mpr rfl⟩

theorem delta_copy (v : Atom 0 → Bool) : Delta v (copy v) = ∅ := by
  ext p
  show (Form.eval v p ≠ Form.eval v p) ↔ p ∈ (∅ : Set (Lang 0))
  simp

/-- The copy context is the *unique* relaxed model that changes nothing. -/
theorem eq_copy_of_delta_empty {v : Atom 0 → Bool} {A : Set (Lang 0)}
    {N : Atom 1 → Bool} (h : N ∈ Mod v A) (hD : Delta v N = ∅) : N = copy v :=
  delta_injOn h (copy_mem v A) (by rw [hD, delta_copy])

/-- **Collapse.**  For every relaxation set `A`, the copy context is the
⊆-minimum of the relaxed models.  Preferring minimal change therefore returns
the unrelaxed tower no matter what was relaxed: circumscribing the abnormality
recovers exactly the case McCarthy calls pointless. -/
theorem copy_minimal (v : Atom 0 → Bool) (A : Set (Lang 0)) :
    copy v ∈ Mod v A ∧ ∀ N ∈ Mod v A, Delta v (copy v) ⊆ Delta v N := by
  refine ⟨copy_mem v A, fun N _ => ?_⟩
  rw [delta_copy]
  exact Set.empty_subset _

/-! ## 5. Specifying the change set determines the context -/

/-- **Forced relaxation.**  Exactly one relaxed model changes *precisely* `A`.
Determinacy is therefore recovered not by minimising change but by naming it --
which is what a logic of relaxing contexts has to supply. -/
theorem forced_unique (v : Atom 0 → Bool) (A : Set (Lang 0)) :
    ∃! N : Atom 1 → Bool, N ∈ Mod v A ∧ Delta v N = A := by
  obtain ⟨N, hN, hD⟩ := delta_surjOn v A A (subset_refl A)
  refine ⟨N, ⟨hN, hD⟩, ?_⟩
  rintro N' ⟨hN', hD'⟩
  exact delta_injOn hN' hN (by rw [hD', hD])

/-! ## Verification -/

section Verification

/-- Non-vacuity: relaxed models other than the copy context exist as soon as
something is relaxed. -/
example (v : Atom 0 → Bool) (a : Lang 0) :
    ∃ N : Atom 1 → Bool, N ∈ Mod v {a} ∧ N ≠ copy v := by
  obtain ⟨N, hN, hD⟩ := delta_surjOn v {a} {a} (subset_refl _)
  refine ⟨N, hN, fun hEq => ?_⟩
  -- `a` is in `N`'s change set, but the copy context changes nothing.
  have ha : a ∈ Delta v N := by rw [hD]; rfl
  rw [hEq, delta_copy] at ha
  exact ha

#print axioms delta_subset
#print axioms mod_iff
#print axioms delta_injOn
#print axioms delta_surjOn
#print axioms copy_minimal
#print axioms forced_unique

end Verification

end TranscendenceTower.MinimalChange
