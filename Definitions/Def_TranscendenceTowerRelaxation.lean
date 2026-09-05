/-
Contexts that extend a level of McCarthy's transcendence tower.

The transcendence tower is proved consistent for the schema in which each
context faithfully copies the one below.  McCarthy identifies the *interesting*
case as the one where a transcending context relaxes or changes an assumption of
the old -- dropping an implicit gravitational field, in his example.  These
definitions give the vocabulary for stating what that means: a level-1 valuation
that agrees with a given level-0 valuation on the old vocabulary, leaving only
the new `ist₀` atoms at issue.

Definitions only -- every theorem about these lives in a separate submission.
-/

import Definitions.Def_TranscendenceTowerCore

set_option autoImplicit false

open TranscendenceTower

namespace TranscendenceTower.Relaxation

/-- Build a level-1 valuation from its restriction to the old vocabulary and its
action on the new `ist₀` atoms.

Declared with `Atom 1 → Bool` as its stated result type on purpose: the
elaborator reduces `Atom 1` to `Atom 0 ⊕ Form (Atom 0)` once, here, so callers
never have to fight the transparency level. -/
def mk1 (v : Atom 0 → Bool) (g : Lang 0 → Bool) : Atom 1 → Bool := Sum.elim v g

/-- `N` is a level-1 valuation whose restriction to the level-0 vocabulary is
`v`: the transcending context still talks about everything the old context did,
and agrees with it there.  Only the new `ist₀` atoms are left open, which is
exactly where relaxation can happen. -/
def ExtendsBase (v : Atom 0 → Bool) (N : Atom 1 → Bool) : Prop :=
  ∀ x : Atom 0, N (Sum.inl x) = v x

end TranscendenceTower.Relaxation
