import Definitions.Def_TranscendenceTowerTransfinite

set_option autoImplicit false

open TranscendenceTower.Transfinite

/-- A biconditional is true exactly when its sides agree. -/
theorem val_iff' (v0 : Nat → Bool) (p q : TForm) :
    val v0 (TForm.iff p q) = true ↔ val v0 p = val v0 q := by
  simp only [TForm.iff, val]
  cases hp : val v0 p <;> cases hq : val v0 q <;> simp

/-- Every instance of the schema is true in the tower model, at every stage. -/
theorem val_schema' (v0 : Nat → Bool) (β : Ordinal) (p : TForm) :
    val v0 (schema β p) = true := by
  rw [schema, val_iff']
  rfl

theorem solution : ∀ (α : Ordinal), ∃ v : TForm → Bool, ∀ q ∈ Gamma α, v q = true := by
  intro α
  refine ⟨val (fun _ => false), ?_⟩
  rintro q ⟨β, p, _, _, rfl⟩
  exact val_schema' _ β p
