/-
The standard default-reasoning example, as a pair of contexts.

Three atoms -- the subject is a bird, it flies, it is abnormal -- and the default
rule that a bird flies unless abnormal.  The smaller context asserts only that
we have a bird together with the default; the larger context additionally
asserts abnormality.

This is the classic illustration of defeasible inference, set up here so that the
effect of *relaxing* the abnormality assumption can be stated as a theorem about
the two contexts.

Definitions only -- every theorem about these lives in a separate submission.
-/

import Definitions.Def_TranscendenceTowerContextTheories

set_option autoImplicit false

open TranscendenceTower

namespace TranscendenceTower.ContextTheories

/-- Atom `0`: the subject is a bird. -/
def bird : L0 := Form.atom 0
/-- Atom `1`: the subject flies. -/
def flies : L0 := Form.atom 1
/-- Atom `2`: the subject is abnormal.  The only abnormality atom. -/
def abn : L0 := Form.atom 2

/-- The default rule: a bird flies unless abnormal. -/
def defaultRule : L0 := Form.impl (Form.conj bird (Form.neg abn)) flies

/-- The designated abnormality atoms. -/
def abAtoms : Set Base := {2}

/-- The smaller context: a bird, and the default. -/
def Tsmall : Set L0 := {bird, defaultRule}

/-- The larger context: additionally, the subject is abnormal. -/
def Tbig : Set L0 := {bird, defaultRule, abn}

/-- The normal witness: a bird that flies and is not abnormal. -/
def vNormal : Val := fun k => k == 0 || k == 1

/-- The abnormal witness: a bird that is abnormal and does not fly. -/
def vAbnormal : Val := fun k => k == 0 || k == 2

end TranscendenceTower.ContextTheories
