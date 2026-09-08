import Definitions.Def_TranscendenceTowerContextUniformity

set_option autoImplicit false
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

namespace TranscendenceTower.UniformityPlatform

variable {A C : Type}


/-! ## The context language -/

namespace CForm


end CForm


/-! ## The base language -/

theorem isBase_neg {p : CForm A C} (h : IsBase p) : IsBase (neg p) := by
  cases p with
  | lit a b => trivial
  | fls => exact ⟨trivial, trivial⟩
  | impl p q => exact ⟨h, trivial⟩
  | ist c p => exact h.elim

/-! ## Substitution

Substitutions act on atoms and are extended homomorphically, acting inside
the scope of `ist`.  A negative literal is sent to the negation of the image
of its atom.  This is the paper's proposition-uniformity apparatus. -/

/-- **The substitution lemma.**  Evaluating a substituted formula is
evaluating the original against the pulled-back valuation. -/
theorem eval_subst (v : CVal A C) (s : A → CForm A C) (p : CForm A C) :
    eval v (subst s p) = eval (pullback v s) p := by
  induction p with
  | lit a b => cases b <;> simp [subst, eval, pullback]
  | fls => rfl
  | impl p q ihp ihq => simp [eval, subst, ihp, ihq]
  | ist c p _ => rfl

/-- Semantic consequence is preserved by substitution. -/
theorem subst_Cn {T : Set (CForm A C)} {p : CForm A C} (s : A → CForm A C)
    (h : p ∈ Cn T) : subst s p ∈ Cn (subst s '' T) := by
  intro v hv
  rw [eval_subst]
  refine h _ fun q hq => ?_
  have := hv (subst s q) ⟨q, hq, rfl⟩
  rwa [eval_subst] at this

/-! ## Freezing a model into a substitution -/

/-- On the base language, the frozen substitution evaluates to `M`
regardless of the ambient valuation: every atom has become a constant. -/
theorem eval_boolSubst (M v : CVal A C) :
    ∀ p : CForm A C, IsBase p → eval v (subst (boolSubst M) p) = eval M p := by
  intro p
  induction p with
  | lit a b =>
    intro _
    cases h : M.atom a <;> cases b <;> simp [subst, boolSubst, h, eval]
  | fls => intro _; rfl
  | impl p q ihp ihq =>
    intro hb
    simp [subst, eval, ihp hb.1, ihq hb.2]
  | ist c p _ => intro hb; exact hb.elim

/-! ## The monotone dichotomy -/

/-- **Monotone dichotomy.**  Let the base theory `T` be context-free and let
the schema's consequents `Γ` be proposition-uniform.  Then either the
extension `Cn (T ∪ Γ)` is inconsistent, or it proves no new base sentence.

Uniformity and novelty are incompatible: a rule indifferent to which
proposition it lifts cannot deliver a particular new fact, because under
substitution it would have to deliver every instance of that fact, and those
are jointly unsatisfiable. -/
theorem monotone_dichotomy {T Γ : Set (CForm A C)}
    (hT : ∀ p ∈ T, IsBase p) (hU : PropUniform Γ)
    (hcon : Consistent (T ∪ Γ)) :
    ∀ φ : CForm A C, IsBase φ → φ ∈ Cn (T ∪ Γ) → φ ∈ Cn T := by
  intro φ hφ hmem
  by_contra hnot
  simp only [Cn, Set.mem_setOf_eq] at hnot
  push Not at hnot
  obtain ⟨M, hMT, hMφ⟩ := hnot
  obtain ⟨v, hv⟩ := hcon
  -- Freeze `M` into a substitution and pull `v` back along it.
  have hmodels : Models (T ∪ Γ) (pullback v (boolSubst M)) := by
    intro q hq
    rw [← eval_subst]
    rcases hq with hq | hq
    · rw [eval_boolSubst M v q (hT q hq)]
      exact hMT q hq
    · exact hv _ (Or.inr (hU (boolSubst M) q hq))
  have h1 : eval (pullback v (boolSubst M)) φ = true := hmem _ hmodels
  rw [← eval_subst, eval_boolSubst M v φ hφ] at h1
  exact hMφ h1

/-- Conservativity, in the paper's formulation: the extension meets the base
language in exactly the base consequences of `T`. -/
theorem conservative {T Γ : Set (CForm A C)}
    (hT : ∀ p ∈ T, IsBase p) (hU : PropUniform Γ)
    (hcon : Consistent (T ∪ Γ)) :
    {φ : CForm A C | IsBase φ ∧ φ ∈ Cn (T ∪ Γ)}
      = {φ : CForm A C | IsBase φ ∧ φ ∈ Cn T} := by
  ext φ
  constructor
  · rintro ⟨hφ, hmem⟩
    exact ⟨hφ, monotone_dichotomy hT hU hcon φ hφ hmem⟩
  · rintro ⟨hφ, hmem⟩
    refine ⟨hφ, fun v hv => hmem v fun q hq => hv q (Or.inl hq)⟩

/-! ## Non-vacuity

The hypotheses are satisfiable by the intended example.  The copy schema —
every context reports the level below faithfully — is proposition-uniform and
consistent, so the theorem says something about it rather than about an empty
class of schemas. -/

theorem copySchema_propUniform : PropUniform (copySchema A C) := by
  rintro s q ⟨c, p, rfl⟩
  exact ⟨c, subst s p, rfl⟩

theorem eval_canonVal (atomv : A → Bool) (p : CForm A C) :
    eval (canonVal atomv) p = canon atomv p := by
  induction p with
  | lit a b => rfl
  | fls => rfl
  | impl p q ihp ihq => simp [eval, canon, ihp, ihq]
  | ist c p _ => rfl

/-- The copy schema is consistent: the canonical valuation models it. -/
theorem copySchema_consistent (atomv : A → Bool) :
    Models (copySchema A C) (canonVal atomv) := by
  rintro q ⟨c, p, rfl⟩
  have hist : eval (canonVal atomv) (CForm.ist c p) = canon atomv p := rfl
  show (!(eval (canonVal atomv) (CForm.ist c p)) || eval (canonVal atomv) p) = true
  rw [hist, eval_canonVal]
  cases h : canon atomv p <;> rfl

/-- So the dichotomy applies non-trivially: with the tautological base and the
copy schema, the hypotheses hold and the conclusion is that nothing new is
derivable at the base. -/
theorem copySchema_conservative (atomv : A → Bool) :
    ∀ φ : CForm A C, IsBase φ → φ ∈ Cn ((∅ : Set (CForm A C)) ∪ copySchema A C) →
      φ ∈ Cn (∅ : Set (CForm A C)) := by
  refine monotone_dichotomy (fun p hp => hp.elim) copySchema_propUniform ?_
  refine ⟨canonVal atomv, fun q hq => ?_⟩
  rcases hq with hq | hq
  · exact hq.elim
  · exact copySchema_consistent atomv q hq

section Verification


end Verification


end TranscendenceTower.UniformityPlatform

open TranscendenceTower.UniformityPlatform

theorem solution (A C : Type) :
    (∀ T Γ : Set (CForm A C), (∀ p ∈ T, IsBase p) → PropUniform Γ →
        Consistent (T ∪ Γ) →
        ∀ φ : CForm A C, IsBase φ → φ ∈ Cn (T ∪ Γ) → φ ∈ Cn T)
    ∧ (∀ T Γ : Set (CForm A C), (∀ p ∈ T, IsBase p) → PropUniform Γ →
        Consistent (T ∪ Γ) →
        {φ : CForm A C | IsBase φ ∧ φ ∈ Cn (T ∪ Γ)}
          = {φ : CForm A C | IsBase φ ∧ φ ∈ Cn T})
    ∧ PropUniform (copySchema A C)
    ∧ (∀ atomv : A → Bool, Models (copySchema A C) (canonVal atomv)) := by
  exact ⟨fun _ _ hT hU hcon => monotone_dichotomy hT hU hcon,
         fun _ _ hT hU hcon => conservative hT hU hcon,
         copySchema_propUniform,
         copySchema_consistent⟩
