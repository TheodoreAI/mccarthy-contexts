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


theorem solution (v : Atom 0 → Bool) (a : Lang 0) :
    ¬ ∃ N : Atom 1 → Bool, ExtendsBase v N ∧
        (∀ p : Lang 0, Form.eval N (schema p) = true) ∧
        N (Sum.inr a) ≠ Form.eval v a := by
  rintro ⟨N, hext, hG, hrel⟩
  exact hrel (((eval_iff' N (ist a) (lift a)).mp (hG a)).trans
    (eval_lift_of_extends' hext a))
