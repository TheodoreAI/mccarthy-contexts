/-
Ordinal-indexed form of McCarthy's transcendence tower.

The finite development indexes the syntax by a type family `Atom : ℕ → Type`.
That does not transpose to ordinals: it would require type-valued transfinite
recursion with an explicit colimit at every limit stage.  Instead we use one
untyped syntax `TForm` together with an inductive membership predicate
`InLang α p` ("p ∈ L_α").  Successor and limit stages are then handled by the
same generation rules, with no case split.

Definitions only -- every theorem about these lives in a separate submission.
-/

import Mathlib.SetTheory.Ordinal.Arithmetic

set_option autoImplicit false

namespace TranscendenceTower.Transfinite

/-- Untyped syntax for the transfinite tower: base atoms `P₀`, an `istβ`
operator for each ordinal `β`, and the classical connectives.  Stratification is
imposed separately by `InLang`, not by the type. -/
inductive TForm : Type 1 where
  | atom : Nat → TForm
  | ist  : Ordinal → TForm → TForm
  | neg  : TForm → TForm
  | conj : TForm → TForm → TForm
  | disj : TForm → TForm → TForm
  | impl : TForm → TForm → TForm

namespace TForm

/-- The biconditional. -/
def iff (p q : TForm) : TForm := conj (impl p q) (impl q p)

end TForm

/-- `InLang α p` says `p ∈ L_α`.

The `ist` rule is the whole content: `istβ(φ)` enters `L_α` only for `β < α` and
`φ ∈ L_β`, so `istβ` can never be applied to anything mentioning `istβ` itself.
This is Tarski's stratification, now indexed by ordinals; successor and limit
stages need no separate clauses. -/
inductive InLang : Ordinal → TForm → Prop where
  | atom {α : Ordinal} (k : Nat) : InLang α (TForm.atom k)
  | ist  {α β : Ordinal} {p : TForm} :
      β < α → InLang β p → InLang α (TForm.ist β p)
  | neg  {α : Ordinal} {p : TForm} : InLang α p → InLang α (TForm.neg p)
  | conj {α : Ordinal} {p q : TForm} :
      InLang α p → InLang α q → InLang α (TForm.conj p q)
  | disj {α : Ordinal} {p q : TForm} :
      InLang α p → InLang α q → InLang α (TForm.disj p q)
  | impl {α : Ordinal} {p q : TForm} :
      InLang α p → InLang α q → InLang α (TForm.impl p q)

/-- A limit ordinal: nonzero, with no greatest element below it.  Stated
directly, so that nothing here depends on Mathlib's repeatedly renamed
successor-ordinal API. -/
def IsLimitOrd (lam : Ordinal) : Prop :=
  0 < lam ∧ ∀ β, β < lam → ∃ γ, β < γ ∧ γ < lam

/-- The instance `istβ(φ) ↔ φ` of the transcendence schema. -/
def schema (β : Ordinal) (p : TForm) : TForm :=
  TForm.iff (TForm.ist β p) p

/-- `Γ_α`: the transcendence schema extended to stage `α`. -/
def Gamma (α : Ordinal) : Set TForm :=
  {q | ∃ β p, β < α ∧ InLang β p ∧ q = schema β p}

/-- The tower valuation, parameterised by an arbitrary assignment `v0` to the
base atoms `P₀`.

Where the finite development builds a chain `M₀ ⊆ M₁ ⊆ ⋯` and takes a direct
limit, here the whole chain is realised at once by a single structural
recursion: the clause `val (istβ p) = val p` is the defining clause of every
successor stage, and because it is one function, the coherence that makes the
limit union well defined holds by construction. -/
def val (v0 : Nat → Bool) : TForm → Bool
  | TForm.atom k   => v0 k
  | TForm.ist _ p  => val v0 p
  | TForm.neg p    => !(val v0 p)
  | TForm.conj p q => (val v0 p) && (val v0 q)
  | TForm.disj p q => (val v0 p) || (val v0 q)
  | TForm.impl p q => !(val v0 p) || (val v0 q)

end TranscendenceTower.Transfinite
