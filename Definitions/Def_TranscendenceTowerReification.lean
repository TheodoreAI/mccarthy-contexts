/-
Reifying a level of McCarthy's transcendence tower: `truths(c₀)` and closure.

McCarthy suggests in passing that the formalism "might be further extended to
provide so that in c₋₁ the whole set of sentences true in c₀ is an object
truths(c₀)".  These definitions set that extension up.  It is where the
deflationary reading of the tower stops applying: reifying a level is not a
definitional extension.

Note on coding: a domain of codes `⌜φ⌝` is posited in the informal treatment,
but no argument depends on which coding is used -- only on there being an
injection -- so codes are identified with the formulas they code and `True₀` is
a set of formulas.  The base language `L₀` is the level-0 language of
`Definitions.Def_TranscendenceTowerCore`, reused rather than redefined.

Definitions only -- every theorem about these lives in a separate submission.
-/

import Definitions.Def_TranscendenceTowerCore
import Mathlib.Data.Set.Basic

set_option autoImplicit false

namespace TranscendenceTower.Reification

/-- The base language `L₀`: propositional formulas over the base atoms `P₀`. -/
abbrev L0 : Type := Form Base

/-- A valuation of `L₀`. -/
abbrev Val : Type := Base → Bool

/-- `truths(c₀)`: the set of `L₀`-sentences true under a valuation.  This is the
object McCarthy proposes to reify. -/
def truths (v : Val) : Set L0 := {p | Form.eval v p = true}

/-- A structure for the reified language `L⁺₀`: a valuation of `L₀` together
with an interpretation of the unary predicate `True₀`.

Tarski's undefinability theorem is sometimes misread as forbidding this.  It
does not: it forbids a sufficiently strong language from defining *its own*
truth predicate.  Here `True₀` lives one level up from the language it
describes, which is precisely the stratified arrangement Tarski proposed as the
remedy. -/
structure RStruc where
  /-- The `L₀`-reduct. -/
  val : Val
  /-- The extension of `True₀`, as a set of codes. -/
  True0 : Set L0

/-- The Tarski schema `T₀ : True₀(⌜φ⌝) ↔ φ`, for every `φ ∈ L₀`. -/
def SatT0 (M : RStruc) : Prop :=
  ∀ p : L0, p ∈ M.True0 ↔ Form.eval M.val p = true

/-- The canonical expansion of a valuation: interpret `True₀` as the set of
codes of its true formulas. -/
def expand (v : Val) : RStruc := ⟨v, truths v⟩

/-- The closure axiom `CL(S) : ∀x (True₀(x) ↔ x ∈ S)`, for an explicitly given
set `S` of codes.

This is a closed-world assumption, and the nonmonotonic machinery it uses is
McCarthy's own invention: `CL(S)` is a circumscription of `True₀`.  The negative
information it supplies -- "nothing else is true here" -- is precisely the
content that cannot be obtained by definitional extension. -/
def SatCL (M : RStruc) (S : Set L0) : Prop :=
  ∀ p : L0, p ∈ M.True0 ↔ p ∈ S

/-- A state-indexed family of reified structures, for relativized closure. -/
structure RFamily (State : Type) where
  /-- The `L₀`-reduct at each state. -/
  val : State → Val
  /-- The extension of `True₀` at each state. -/
  True0 : State → Set L0

/-- `CL(S, c)`: relative to state `c`, the extension of `True₀` is exactly
`S`. -/
def SatCLat {State : Type} (F : RFamily State) (S : Set L0) (c : State) : Prop :=
  ∀ p : L0, p ∈ F.True0 c ↔ p ∈ S

end TranscendenceTower.Reification
