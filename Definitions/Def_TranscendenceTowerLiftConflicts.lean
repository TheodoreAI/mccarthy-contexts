/-
Two contexts that conflict, and a target that does not say how.

The first pair is a flat contradiction: the source asserts an atom and the
target asserts its negation, so the transfer cannot go through untouched.

The second pair is the interesting one.  The source asserts two atoms and the
target asserts only that they are not *both* true.  The conflict is real, but
the target is silent about which of the two to give up -- which is exactly the
situation in which a preference for minimal abnormality has to make a choice,
and, as the accompanying theorem shows, cannot.

Definitions only -- every theorem about these lives in a separate submission.
-/

import Definitions.Def_TranscendenceTowerLifting

set_option autoImplicit false

open TranscendenceTower TranscendenceTower.ContextTheories

namespace TranscendenceTower.Lifting

/-- Atom `0`. -/
def pA : L0 := Form.atom 0
/-- Atom `1`. -/
def qA : L0 := Form.atom 1

/-- A source asserting `p`. -/
def srcP : Set L0 := {pA}
/-- A target asserting `¬p`, contradicting the source outright. -/
def tgtNotP : Set L0 := {Form.neg pA}
/-- A valuation making every atom false. -/
def vNotP : Val := fun _ => false

/-- A source asserting both `p` and `q`. -/
def srcPQ : Set L0 := {pA, qA}
/-- A target asserting that `p` and `q` are not both true. -/
def tgtNand : Set L0 := {Form.neg (Form.conj pA qA)}

/-- `p` true, `q` false. -/
def vP : Val := fun k => k == 0
/-- `q` true, `p` false. -/
def vQ : Val := fun k => k == 1

end TranscendenceTower.Lifting
