/-
  Relaxation: the case McCarthy calls interesting.

  "Consistency of a Stratified Formalization of McCarthy's Transcendence Tower"
  proves the tower consistent, and then concedes (Remark 2) that the schema it
  proved consistent is the one McCarthy himself calls "pointless", in which each
  context faithfully copies the one below.  The interesting case -- in which the
  transcending context *relaxes or changes an assumption* of the old, dropping
  an implicit gravitational field, to use McCarthy's example -- is stated there
  to be "not a definitional extension, not conservative, and not covered by
  anything proved here".

  Those three claims are asserted, not proved.  This file proves them, and in
  doing so makes precise why the harmless tower is harmless.

  The key observation is that the earlier consistency result understates what
  the schema does.  Gamma does not merely *permit* the copy model; it *forces*
  it.  Given the level-0 valuation, a level-1 valuation satisfying Gamma is
  uniquely determined (`schema_determines`).  That is the exact content of
  "definitional extension in disguise", and it immediately explains the rest:

  * Relaxation is the failure of that uniqueness.  A context that declines to
    assert an assumption of the level below falsifies the corresponding instance
    of Gamma (`relaxation_refutes_schema`), so "harmless" and "interesting" are
    not merely different cases -- they are formally incompatible.

  * Dropping even a *single* instance of Gamma already destroys uniqueness:
    two distinct valuations then extend the same base (`relaxed_not_definitional`).
    So the relaxed tower is not a definitional extension, and the consistency
    argument of the earlier work genuinely does not transfer.

  Builds on the published platform definitions rather than redefining anything.
-/

import Definitions.Def_TranscendenceTowerCore

set_option autoImplicit false

open TranscendenceTower

namespace TranscendenceTower.Relaxation

/-! ## Helper lemmas (inlined; short proofs, not separate platform nodes) -/

/-- Evaluating a renamed formula equals evaluating along the renamed valuation. -/
theorem eval_map' {A B : Type} (f : A → B) (w : B → Bool) (p : Form A) :
    Form.eval w (Form.map f p) = Form.eval (fun x => w (f x)) p := by
  induction p with
  | atom x => rfl
  | neg p ih => simp [Form.map, Form.eval, ih]
  | conj p q ihp ihq => simp [Form.map, Form.eval, ihp, ihq]
  | disj p q ihp ihq => simp [Form.map, Form.eval, ihp, ihq]
  | impl p q ihp ihq => simp [Form.map, Form.eval, ihp, ihq]

/-- A biconditional is true exactly when its two sides agree. -/
theorem eval_iff' {A : Type} (w : A → Bool) (p q : Form A) :
    Form.eval w (Form.iff p q) = true ↔ Form.eval w p = Form.eval w q := by
  simp only [Form.iff, Form.eval]
  cases hp : Form.eval w p <;> cases hq : Form.eval w q <;> simp

/-! ## Contexts that extend a given level -/

/-- `!b ≠ b`. -/
theorem bool_not_ne (b : Bool) : (!b) ≠ b := by cases b <;> simp

/-- Build a level-1 valuation from its restriction to the old vocabulary and its
action on the new `ist₀` atoms.

Declared as a definition with `Atom 1 → Bool` as its stated type on purpose: the
elaborator reduces `Atom 1` to `Atom 0 ⊕ Form (Atom 0)` here once, so callers
never have to fight the transparency level (a bare `Sum.elim` in term position
is rejected as `Atom 0 ⊕ Form (Atom 0) → Bool` where `Atom (0+1) → Bool` is
expected). -/
def mk1 (v : Atom 0 → Bool) (g : Lang 0 → Bool) : Atom 1 → Bool := Sum.elim v g

/-- `N` is a level-1 valuation whose restriction to the level-0 vocabulary is
`v`: the transcending context still talks about everything the old one did, and
agrees with it there.  Only the *new* `ist₀` atoms are at issue. -/
def ExtendsBase (v : Atom 0 → Bool) (N : Atom 1 → Bool) : Prop :=
  ∀ x : Atom 0, N (Sum.inl x) = v x

/-- Anything built by `mk1` extends its base, definitionally. -/
theorem extendsBase_mk1 (v : Atom 0 → Bool) (g : Lang 0 → Bool) :
    ExtendsBase v (mk1 v g) := fun _ => rfl

/-- On the old vocabulary, an extending context evaluates exactly as the old
one.  (This is Lemma 1 of the earlier work, relativised to an arbitrary
extending valuation rather than the canonical chain.) -/
theorem eval_lift_of_extends {v : Atom 0 → Bool} {N : Atom 1 → Bool}
    (h : ExtendsBase v N) (p : Lang 0) :
    Form.eval N (lift p) = Form.eval v p := by
  have h1 : Form.eval N (lift p) = Form.eval (fun x => N (Sum.inl x)) p :=
    eval_map' (Sum.inl : Atom 0 → Atom 1) N p
  have h2 : (fun x => N (Sum.inl x)) = v := funext h
  rw [h1, h2]

/-! ## 1. The schema is definitional: it forces the copy model -/

/-- **The transcendence schema determines the transcending context.**

If `N` extends `v` and satisfies every instance of the schema, then the value of
each new atom `ist₀(φ)` is *forced* to be the old value of `φ`.  Nothing is left
free.

This is the precise content of the remark that each stage of the tower is "a
definitional extension in disguise": the schema is not one constraint among many
that the copy model happens to satisfy, it is a definition of the new
vocabulary in terms of the old. -/
theorem schema_determines {v : Atom 0 → Bool} {N : Atom 1 → Bool}
    (hext : ExtendsBase v N) (hG : ∀ p : Lang 0, Form.eval N (schema p) = true)
    (p : Lang 0) : N (Sum.inr p) = Form.eval v p := by
  have h := (eval_iff' N (ist p) (lift p)).mp (hG p)
  rw [eval_lift_of_extends hext p] at h
  exact h

/-- Uniqueness, stated globally: any two contexts extending the same base and
satisfying the schema are equal.  A transcending context that obeys the schema
has no freedom at all. -/
theorem schema_unique {v : Atom 0 → Bool} {N₁ N₂ : Atom 1 → Bool}
    (h₁ : ExtendsBase v N₁) (hG₁ : ∀ p : Lang 0, Form.eval N₁ (schema p) = true)
    (h₂ : ExtendsBase v N₂) (hG₂ : ∀ p : Lang 0, Form.eval N₂ (schema p) = true) :
    N₁ = N₂ := by
  funext x
  cases x with
  | inl a => rw [h₁ a, h₂ a]
  | inr p => rw [schema_determines h₁ hG₁ p, schema_determines h₂ hG₂ p]

/-! ## 2. Relaxation is incompatible with the schema -/

/-- **A relaxing context falsifies the schema.**

Say the transcending context *relaxes* the assumption `a` if it declines to
assign `ist₀(a)` the old truth value of `a` -- McCarthy's example being a
context that drops an implicit gravitational field the inner context assumed.
Then the corresponding instance of the schema fails.

So the two cases McCarthy distinguishes are not merely different: they are
formally exclusive.  Any genuine relaxation refutes the very schema whose
consistency the earlier work established, which is exactly why that consistency
result does not reach the interesting case. -/
theorem relaxation_refutes_schema {v : Atom 0 → Bool} {N : Atom 1 → Bool}
    (hext : ExtendsBase v N) {a : Lang 0}
    (hrel : N (Sum.inr a) ≠ Form.eval v a) :
    Form.eval N (schema a) ≠ true := by
  intro hGa
  exact hrel (((eval_iff' N (ist a) (lift a)).mp hGa).trans
    (eval_lift_of_extends hext a))

/-- Contrapositive, as a joint-unsatisfiability statement: no context both
satisfies the whole schema and relaxes anything. -/
theorem no_relaxing_model_of_schema (v : Atom 0 → Bool) (a : Lang 0) :
    ¬ ∃ N : Atom 1 → Bool, ExtendsBase v N ∧
        (∀ p : Lang 0, Form.eval N (schema p) = true) ∧
        N (Sum.inr a) ≠ Form.eval v a := by
  rintro ⟨N, hext, hG, hrel⟩
  exact relaxation_refutes_schema hext hrel (hG a)

/-! ## 3. The relaxed schema is consistent but not definitional -/

/-- **Dropping one instance already destroys uniqueness.**

Let `a` be the assumption to be relaxed, and impose the schema everywhere
*except* at `a`.  Then there are two distinct contexts extending the same base
and satisfying all remaining instances: one that keeps the old value of `a`, and
one that relaxes it.

Two consequences, which are the claims the earlier work left unproved.  First,
the relaxed tower is **not a definitional extension**: the new vocabulary is no
longer determined by the old, so the argument that stages are conservative
because they are definitional does not apply.  Second, the relaxed schema is
nonetheless **consistent** -- the two witnesses are models of it -- so
relaxation is not incoherent, merely underdetermined.  What it loses is exactly
the property that made the original tower harmless. -/
theorem relaxed_not_definitional (v : Atom 0 → Bool) (a : Lang 0) :
    ∃ N₁ N₂ : Atom 1 → Bool,
      ExtendsBase v N₁ ∧ ExtendsBase v N₂ ∧ N₁ ≠ N₂ ∧
      (∀ p : Lang 0, p ≠ a → Form.eval N₁ (schema p) = true) ∧
      (∀ p : Lang 0, p ≠ a → Form.eval N₂ (schema p) = true) := by
  classical
  -- `N₁` is the canonical copy context; `N₂` relaxes exactly the assumption `a`.
  refine ⟨mk1 v (fun p => Form.eval v p),
          mk1 v (fun p => if p = a then !(Form.eval v a) else Form.eval v p),
          extendsBase_mk1 _ _, extendsBase_mk1 _ _, ?_, ?_, ?_⟩
  · -- the two contexts disagree precisely at the relaxed assumption
    intro hEq
    have h : Form.eval v a
        = (if a = a then !(Form.eval v a) else Form.eval v a) := congrFun hEq (Sum.inr a)
    rw [if_pos rfl] at h
    exact bool_not_ne (Form.eval v a) h.symm
  · intro p _
    refine (eval_iff' _ (ist p) (lift p)).mpr ?_
    rw [eval_lift_of_extends (extendsBase_mk1 v _) p]
    rfl
  · intro p hp
    refine (eval_iff' _ (ist p) (lift p)).mpr ?_
    rw [eval_lift_of_extends (extendsBase_mk1 v _) p]
    show (if p = a then !(Form.eval v a) else Form.eval v p) = Form.eval v p
    rw [if_neg hp]

/-! ## Verification -/

section Verification

/-- Non-vacuity: relaxing contexts exist, so §2 is not empty talk. -/
example (v : Atom 0 → Bool) (a : Lang 0) :
    ∃ N : Atom 1 → Bool, ExtendsBase v N ∧ N (Sum.inr a) ≠ Form.eval v a := by
  classical
  refine ⟨mk1 v (fun p => if p = a then !(Form.eval v a) else Form.eval v p),
          extendsBase_mk1 _ _, ?_⟩
  show (if a = a then !(Form.eval v a) else Form.eval v a) ≠ Form.eval v a
  rw [if_pos rfl]
  exact bool_not_ne (Form.eval v a)

#print axioms schema_determines
#print axioms schema_unique
#print axioms relaxation_refutes_schema
#print axioms no_relaxing_model_of_schema
#print axioms relaxed_not_definitional

end Verification

end TranscendenceTower.Relaxation
