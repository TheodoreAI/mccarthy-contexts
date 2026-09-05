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


theorem bool_not_ne' (b : Bool) : (!b) ≠ b := by cases b <;> simp

theorem extendsBase_mk1' (v : Atom 0 → Bool) (g : Lang 0 → Bool) :
    ExtendsBase v (mk1 v g) := fun _ => rfl

theorem solution (v : Atom 0 → Bool) (a : Lang 0) :
    ∃ N₁ N₂ : Atom 1 → Bool,
      ExtendsBase v N₁ ∧ ExtendsBase v N₂ ∧ N₁ ≠ N₂ ∧
      (∀ p : Lang 0, p ≠ a → Form.eval N₁ (schema p) = true) ∧
      (∀ p : Lang 0, p ≠ a → Form.eval N₂ (schema p) = true) := by
  classical
  refine ⟨mk1 v (fun p => Form.eval v p),
          mk1 v (fun p => if p = a then !(Form.eval v a) else Form.eval v p),
          extendsBase_mk1' _ _, extendsBase_mk1' _ _, ?_, ?_, ?_⟩
  · intro hEq
    have h : Form.eval v a
        = (if a = a then !(Form.eval v a) else Form.eval v a) := congrFun hEq (Sum.inr a)
    rw [if_pos rfl] at h
    exact bool_not_ne' (Form.eval v a) h.symm
  · intro p _
    refine (eval_iff' _ (ist p) (lift p)).mpr ?_
    rw [eval_lift_of_extends' (extendsBase_mk1' v _) p]
    rfl
  · intro p hp
    refine (eval_iff' _ (ist p) (lift p)).mpr ?_
    rw [eval_lift_of_extends' (extendsBase_mk1' v _) p]
    show (if p = a then !(Form.eval v a) else Form.eval v p) = Form.eval v p
    rw [if_neg hp]
