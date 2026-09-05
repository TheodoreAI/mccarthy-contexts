/-
Core definitions for a stratified formalization of McCarthy's transcendence
tower: the cumulative tower of propositional languages `L₀ ⊆ L₁ ⊆ ⋯`, the
`istₙ` operator, the transcendence schema, and the chain of valuations.

Definitions only -- every theorem about these lives in a separate submission.
-/

set_option autoImplicit false

namespace TranscendenceTower

/-- Classical propositional formulas over an atom type `A`. -/
inductive Form (A : Type) : Type where
  | atom : A → Form A
  | neg  : Form A → Form A
  | conj : Form A → Form A → Form A
  | disj : Form A → Form A → Form A
  | impl : Form A → Form A → Form A

namespace Form

/-- Renaming of atoms; realises the inclusion `Lₙ ⊆ Lₙ₊₁`. -/
def map {A B : Type} (f : A → B) : Form A → Form B
  | atom a   => atom (f a)
  | neg p    => neg (map f p)
  | conj p q => conj (map f p) (map f q)
  | disj p q => disj (map f p) (map f q)
  | impl p q => impl (map f p) (map f q)

/-- The biconditional. -/
def iff {A : Type} (p q : Form A) : Form A :=
  conj (impl p q) (impl q p)

/-- Classical truth-table evaluation under a valuation of the atoms. -/
def eval {A : Type} (v : A → Bool) : Form A → Bool
  | atom a   => v a
  | neg p    => !(eval v p)
  | conj p q => (eval v p) && (eval v q)
  | disj p q => (eval v p) || (eval v q)
  | impl p q => !(eval v p) || (eval v q)

end Form

/-- The base atoms `P₀ = {p₁, p₂, …}`, countably many. -/
abbrev Base : Type := Nat

/-- The cumulative tower of atom sets: `A₀ = P₀` and
`Aₙ₊₁ = Aₙ ∪ {istₙ φ : φ ∈ Lₙ}`.  The sum type makes cumulativity automatic --
`Aₙ₊₁` retains every atom of `Aₙ` in its left summand, which is what makes the
languages form a chain. -/
def Atom : Nat → Type
  | 0     => Base
  | n + 1 => Sum (Atom n) (Form (Atom n))

/-- `Lₙ`: the propositional language of level `n`. -/
abbrev Lang (n : Nat) : Type := Form (Atom n)

/-- The inclusion `Lₙ ⊆ Lₙ₊₁`. -/
def lift {n : Nat} (p : Lang n) : Lang (n + 1) :=
  Form.map Sum.inl p

/-- `istₙ φ`, read "φ is true in `c₋ₙ`", as a formula of `Lₙ₊₁`.

`istₙ` is typed so that it may only be applied to arguments drawn from `Lₙ`:
no formula can assert `istₙ` of itself.  This is Tarski's stratification, and it
is why no analogue of the Liar sentence can be written down. -/
def ist {n : Nat} (p : Lang n) : Lang (n + 1) :=
  Form.atom (Sum.inr p)

/-- The instance `istₙ(φ) ↔ φ` of the transcendence schema `Γ`. -/
def schema {n : Nat} (p : Lang n) : Lang (n + 1) :=
  Form.iff (ist p) (lift p)

/-- The increasing chain of classical valuations `M₀ ⊆ M₁ ⊆ ⋯`.

`M₀` sends every base atom to `false`.  `Mₙ₊₁` keeps `Mₙ`'s values on every old
atom and sets `Mₙ₊₁(istₙ φ) = Mₙ(φ)` -- well defined because `φ` ranges only
over `Lₙ`, on which `Mₙ` was already fixed one stage earlier. -/
def M : (n : Nat) → Atom n → Bool
  | 0     => fun _ => false
  | n + 1 => Sum.elim (M n) (fun p => Form.eval (M n) p)

/-- The iterated inclusion `Lₙ ⊆ Lₙ₊ₖ`. -/
def liftAdd {n : Nat} : (k : Nat) → Lang n → Lang (n + k)
  | 0,     p => p
  | k + 1, p => lift (liftAdd k p)

end TranscendenceTower
