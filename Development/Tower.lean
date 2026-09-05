/-
  Consistency of a stratified formalization of McCarthy's transcendence tower.

  Formalizes Definitions 1-2, Lemma 1 and Theorem 1 of
  "Consistency of a Stratified Formalization of McCarthy's Transcendence Tower",
  which makes precise McCarthy's assertion (Notes on Formalizing Context, 1993)
  that the regress c_0, c_{-1}, c_{-2}, ... "is infinite, but ... harmless".

  Deliberately elementary: no compactness, no Mathlib. The model is a direct
  limit of an increasing chain of classical valuations.

  Note: the platform elaborates with `autoImplicit false`, so every type
  variable is declared explicitly.
-/

set_option autoImplicit false

namespace TranscendenceTower

/-! ## Propositional syntax over an arbitrary atom type -/

/-- Classical propositional formulas over an atom type `A`. -/
inductive Form (A : Type) : Type where
  | atom : A → Form A
  | neg  : Form A → Form A
  | conj : Form A → Form A → Form A
  | disj : Form A → Form A → Form A
  | impl : Form A → Form A → Form A

namespace Form

/-- Renaming of atoms; this is what realises an inclusion `Lₙ ⊆ Lₙ₊₁`. -/
def map {A B : Type} (f : A → B) : Form A → Form B
  | atom a   => atom (f a)
  | neg p    => neg (map f p)
  | conj p q => conj (map f p) (map f q)
  | disj p q => disj (map f p) (map f q)
  | impl p q => impl (map f p) (map f q)

/-- The biconditional, defined as usual. -/
def iff {A : Type} (p q : Form A) : Form A :=
  conj (impl p q) (impl q p)

/-- Classical truth-table evaluation under a valuation of the atoms. -/
def eval {A : Type} (v : A → Bool) : Form A → Bool
  | atom a   => v a
  | neg p    => !(eval v p)
  | conj p q => (eval v p) && (eval v q)
  | disj p q => (eval v p) || (eval v q)
  | impl p q => !(eval v p) || (eval v q)

/-- Evaluating a renamed formula = evaluating along the renamed valuation. -/
theorem eval_map {A B : Type} (f : A → B) (v : B → Bool) (p : Form A) :
    eval v (map f p) = eval (fun a => v (f a)) p := by
  induction p with
  | atom a => rfl
  | neg p ih => simp [map, eval, ih]
  | conj p q ihp ihq => simp [map, eval, ihp, ihq]
  | disj p q ihp ihq => simp [map, eval, ihp, ihq]
  | impl p q ihp ihq => simp [map, eval, ihp, ihq]

/-- A biconditional is true exactly when its two sides agree. -/
theorem eval_iff {A : Type} (v : A → Bool) (p q : Form A) :
    eval v (iff p q) = true ↔ eval v p = eval v q := by
  simp only [iff, eval]
  cases hp : eval v p <;> cases hq : eval v q <;> simp

end Form

/-! ## Definition 1 — the tower of languages -/

/-- The base atoms `P₀ = {p₁, p₂, …}`, countably many. -/
abbrev Base : Type := Nat

/-- **Definition 1.** The cumulative tower of atom sets:
`A₀ = P₀` and `Aₙ₊₁ = Aₙ ∪ {istₙ φ : φ ∈ Lₙ}`.

The sum type makes cumulativity automatic — `Aₙ₊₁` retains every atom of `Aₙ`
(including all `istₖ` atoms for `k < n`) in its left summand, which is exactly
what makes the languages form a chain. -/
def Atom : Nat → Type
  | 0     => Base
  | n + 1 => Sum (Atom n) (Form (Atom n))

/-- `Lₙ`: the propositional language of level `n`. -/
abbrev Lang (n : Nat) : Type := Form (Atom n)

/-- The inclusion `Lₙ ⊆ Lₙ₊₁`. -/
def lift {n : Nat} (p : Lang n) : Lang (n + 1) :=
  Form.map Sum.inl p

/-- `istₙ φ`, read "φ is true in `c₋ₙ`", as a formula of `Lₙ₊₁`.

Crucially `istₙ` is applied only to arguments drawn from `Lₙ`: it is *typed*
so that no formula can assert `istₙ` of itself. This is Tarski's stratification,
and it is why no analogue of the Liar can even be written down. -/
def ist {n : Nat} (p : Lang n) : Lang (n + 1) :=
  Form.atom (Sum.inr p)

/-! ## Definition 2 — the transcendence schema -/

/-- **Definition 2.** The instance `istₙ(φ) ↔ φ` of the transcendence schema Γ,
the formal content of McCarthy's stipulation that unconditional belief in `p`
at one level is equivalent to `ist` of `p` one level up. -/
def schema {n : Nat} (p : Lang n) : Lang (n + 1) :=
  Form.iff (ist p) (lift p)

/-! ## The model -/

/-- The increasing chain of classical valuations `M₀ ⊆ M₁ ⊆ ⋯`.

`M₀` sends every base atom to `false` (any assignment would do). `Mₙ₊₁` keeps
`Mₙ`'s values on every old atom and sets `Mₙ₊₁(istₙ φ) = Mₙ(φ)` — well defined
because `φ` ranges only over `Lₙ`, on which `Mₙ` was already fixed one stage
earlier. There is no circularity. -/
def M : (n : Nat) → Atom n → Bool
  | 0     => fun _ => false
  | n + 1 => Sum.elim (M n) (fun p => Form.eval (M n) p)

/-- The defining clause of `Mₙ₊₁` on the new atoms, by definitional unfolding. -/
theorem eval_ist {n : Nat} (p : Lang n) :
    Form.eval (M (n + 1)) (ist p) = Form.eval (M n) p := rfl

/-- **Lemma 1.** `Mₙ₊₁` agrees with `Mₙ` on all of `Lₙ`: `Mₙ₊₁ ↾ Lₙ = Mₙ`.

The only atoms on which `Mₙ₊₁` makes a genuinely new choice are the `istₙ(φ)`,
none of which occur in `Lₙ`. -/
theorem eval_lift {n : Nat} (p : Lang n) :
    Form.eval (M (n + 1)) (lift p) = Form.eval (M n) p :=
  -- Term mode on purpose: `rw` will not unfold `Atom (n+1)` to
  -- `Atom n ⊕ Form (Atom n)` at `implicit` transparency, but `exact`/term
  -- elaboration checks defeq at default transparency, where it does reduce.
  Form.eval_map (Sum.inl : Atom n → Atom (n + 1)) (M (n + 1)) p

/-! ## Theorem 1 -/

/-- **Theorem 1.** Every instance of the transcendence schema Γ is true in the
tower model; hence Γ is satisfiable, and therefore consistent. -/
theorem schema_true {n : Nat} (p : Lang n) :
    Form.eval (M (n + 1)) (schema p) = true := by
  rw [schema, Form.eval_iff, eval_ist, eval_lift]

/-- Theorem 1, stated as satisfiability of the whole schema. -/
theorem transcendence_tower_satisfiable :
    ∀ (n : Nat) (p : Lang n), Form.eval (M (n + 1)) (schema p) = true :=
  fun _ p => schema_true p

/-! ## Coherence: `M_ω` is well defined -/

/-- The iterated inclusion `Lₙ ⊆ Lₙ₊ₖ`. -/
def liftAdd {n : Nat} : (k : Nat) → Lang n → Lang (n + k)
  | 0,     p => p
  | k + 1, p => lift (liftAdd k p)

/-- The chain is coherent: the truth value of a formula does not depend on the
stage at which it is viewed. This is what makes `M_ω := ⋃ₙ Mₙ` well defined on
`L_ω = ⋃ₙ Lₙ`, and it is the only place the limit stage could have gone wrong. -/
theorem eval_liftAdd {n : Nat} (k : Nat) (p : Lang n) :
    Form.eval (M (n + k)) (liftAdd k p) = Form.eval (M n) p := by
  induction k with
  | zero => rfl
  | succ k ih =>
      exact (eval_lift (liftAdd k p)).trans ih

end TranscendenceTower

/-! ## Verification section

Independent restatements of the headline results (guarding against a name
meaning something other than advertised), plus axiom audits: each must report
only Lean's standard axioms, and in particular must NOT list `sorryAx`. -/

section Verification
open TranscendenceTower

/-- Theorem 1 restated inline, with the schema unfolded to `istₙ(φ) ↔ φ`. -/
example : ∀ (n : Nat) (p : Lang n),
    Form.eval (M (n + 1)) (Form.iff (ist p) (lift p)) = true :=
  fun _ p => schema_true p

/-- Coherence restated inline. -/
example : ∀ (n k : Nat) (p : Lang n),
    Form.eval (M (n + k)) (liftAdd k p) = Form.eval (M n) p :=
  fun _ k p => eval_liftAdd k p

#print axioms Form.eval_map
#print axioms Form.eval_iff
#print axioms eval_ist
#print axioms eval_lift
#print axioms schema_true
#print axioms transcendence_tower_satisfiable
#print axioms eval_liftAdd

end Verification
