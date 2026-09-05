import Definitions.Def_TranscendenceTowerCore

set_option autoImplicit false

open TranscendenceTower

/-- Evaluating a renamed formula equals evaluating along the renamed
valuation. -/
theorem eval_map' {A B : Type} (f : A → B) (v : B → Bool) (p : Form A) :
    Form.eval v (Form.map f p) = Form.eval (fun a => v (f a)) p := by
  induction p with
  | atom a => rfl
  | neg p ih => simp [Form.map, Form.eval, ih]
  | conj p q ihp ihq => simp [Form.map, Form.eval, ihp, ihq]
  | disj p q ihp ihq => simp [Form.map, Form.eval, ihp, ihq]
  | impl p q ihp ihq => simp [Form.map, Form.eval, ihp, ihq]

/-- A biconditional is true exactly when its two sides agree. -/
theorem eval_iff' {A : Type} (v : A → Bool) (p q : Form A) :
    Form.eval v (Form.iff p q) = true ↔ Form.eval v p = Form.eval v q := by
  simp only [Form.iff, Form.eval]
  cases hp : Form.eval v p <;> cases hq : Form.eval v q <;> simp

/-- The defining clause of `Mₙ₊₁` on the new atoms, by definitional
unfolding. -/
theorem eval_ist' {n : Nat} (p : Lang n) :
    Form.eval (M (n + 1)) (ist p) = Form.eval (M n) p := rfl

/-- Lemma 1: `Mₙ₊₁` agrees with `Mₙ` on all of `Lₙ`.

Term mode on purpose: `rw` will not unfold `Atom (n+1)` to
`Atom n ⊕ Form (Atom n)` at `implicit` transparency, but term elaboration
checks definitional equality at default transparency, where it does reduce. -/
theorem eval_lift' {n : Nat} (p : Lang n) :
    Form.eval (M (n + 1)) (lift p) = Form.eval (M n) p :=
  eval_map' (Sum.inl : Atom n → Atom (n + 1)) (M (n + 1)) p

theorem solution : ∀ (n : Nat) (p : Lang n),
    Form.eval (M (n + 1)) (schema p) = true := by
  intro n p
  rw [schema, eval_iff', eval_ist', eval_lift']
