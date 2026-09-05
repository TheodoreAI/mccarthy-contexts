import Definitions.Def_TranscendenceTowerRelaxation

set_option autoImplicit false

open TranscendenceTower TranscendenceTower.Relaxation

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

theorem eval_lift_of_extends' {v : Atom 0 → Bool} {N : Atom 1 → Bool}
    (h : ExtendsBase v N) (p : Lang 0) :
    Form.eval N (lift p) = Form.eval v p := by
  have h1 : Form.eval N (lift p) = Form.eval (fun x => N (Sum.inl x)) p :=
    eval_map' (Sum.inl : Atom 0 → Atom 1) N p
  have h2 : (fun x => N (Sum.inl x)) = v := funext h
  rw [h1, h2]

/-- The schema forces the value of every new atom. -/
theorem schema_determines' {v : Atom 0 → Bool} {N : Atom 1 → Bool}
    (hext : ExtendsBase v N) (hG : ∀ p : Lang 0, Form.eval N (schema p) = true)
    (p : Lang 0) : N (Sum.inr p) = Form.eval v p := by
  have h := (eval_iff' N (ist p) (lift p)).mp (hG p)
  rw [eval_lift_of_extends' hext p] at h
  exact h

theorem solution (v : Atom 0 → Bool) (N₁ N₂ : Atom 1 → Bool)
    (h₁ : ExtendsBase v N₁) (hG₁ : ∀ p : Lang 0, Form.eval N₁ (schema p) = true)
    (h₂ : ExtendsBase v N₂) (hG₂ : ∀ p : Lang 0, Form.eval N₂ (schema p) = true) :
    N₁ = N₂ := by
  funext x
  cases x with
  | inl a => rw [h₁ a, h₂ a]
  | inr p => rw [schema_determines' h₁ hG₁ p, schema_determines' h₂ hG₂ p]
