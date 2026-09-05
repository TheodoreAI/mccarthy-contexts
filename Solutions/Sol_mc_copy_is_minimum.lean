import Definitions.Def_TranscendenceTowerMinimalChange

set_option autoImplicit false

open TranscendenceTower TranscendenceTower.Relaxation TranscendenceTower.MinimalChange

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

theorem schema_iff {v : Atom 0 → Bool} {N : Atom 1 → Bool} (hext : ExtendsBase v N)
    (p : Lang 0) :
    Form.eval N (schema p) = true ↔ N (Sum.inr p) = Form.eval v p := by
  rw [show schema p = Form.iff (ist p) (lift p) from rfl, eval_iff' N (ist p) (lift p),
    eval_lift_of_extends hext p]
  exact Iff.rfl

theorem bool_ne_iff (b c : Bool) : b ≠ c ↔ b = !c := by
  cases b <;> cases c <;> simp

theorem extendsBase_mk1 (v : Atom 0 → Bool) (g : Lang 0 → Bool) :
    ExtendsBase v (mk1 v g) := fun _ => rfl

theorem delta_subset' {v : Atom 0 → Bool} {A : Set (Lang 0)} {N : Atom 1 → Bool}
    (h : N ∈ Mod v A) : Delta v N ⊆ A := by
  intro p hp
  by_contra hpA
  exact hp ((schema_iff h.1 p).mp (h.2 p hpA))

theorem delta_inj' {v : Atom 0 → Bool} {A : Set (Lang 0)} {N₁ N₂ : Atom 1 → Bool}
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

theorem delta_surj' (v : Atom 0 → Bool) (A S : Set (Lang 0)) (hSA : S ⊆ A) :
    ∃ N : Atom 1 → Bool, N ∈ Mod v A ∧ Delta v N = S := by
  classical
  refine ⟨mk1 v (fun p => if p ∈ S then !(Form.eval v p) else Form.eval v p), ?_, ?_⟩
  · refine ⟨extendsBase_mk1 _ _, fun p hpA => (schema_iff (extendsBase_mk1 v _) p).mpr ?_⟩
    show (if p ∈ S then !(Form.eval v p) else Form.eval v p) = Form.eval v p
    rw [if_neg (fun hpS => hpA (hSA hpS))]
  · ext p
    show (if p ∈ S then !(Form.eval v p) else Form.eval v p) ≠ Form.eval v p ↔ p ∈ S
    by_cases hpS : p ∈ S
    · rw [if_pos hpS]; simp [hpS]
    · rw [if_neg hpS]; simp [hpS]

theorem copy_mem' (v : Atom 0 → Bool) (A : Set (Lang 0)) : copy v ∈ Mod v A :=
  ⟨extendsBase_mk1 _ _, fun p _ => (schema_iff (extendsBase_mk1 v _) p).mpr rfl⟩

theorem delta_copy' (v : Atom 0 → Bool) : Delta v (copy v) = ∅ := by
  ext p
  show (Form.eval v p ≠ Form.eval v p) ↔ p ∈ (∅ : Set (Lang 0))
  simp


theorem solution (v : Atom 0 → Bool) (A : Set (Lang 0)) :
    copy v ∈ Mod v A ∧ Delta v (copy v) = ∅
      ∧ (∀ N ∈ Mod v A, Delta v N = ∅ → N = copy v)
      ∧ (∀ N ∈ Mod v A, Delta v (copy v) ⊆ Delta v N) := by
  refine ⟨copy_mem' v A, delta_copy' v, ?_, ?_⟩
  · intro N hN hD
    exact delta_inj' hN (copy_mem' v A) (by rw [hD, delta_copy'])
  · intro N _
    rw [delta_copy' v]
    exact Set.empty_subset _
