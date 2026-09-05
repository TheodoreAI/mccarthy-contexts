/-
Lifting facts between contexts, with an abnormality guard.

McCarthy's `specializes` axiom is a default rule for transferring facts between
contexts:

    specializes(c₁,c₂) ∧ ¬ab(p,c₁,c₂) ∧ ist(c₁,p) → ist(c₂,p)

"what holds in a context still holds in a more specific one, unless it is
abnormal for that transfer".  These definitions model such a transfer.  Nothing
here presupposes that the two contexts are stacked: the Sherlock Holmes context
and the US-legal-history context are siblings, and `specializes` relates
contexts of that kind too.

A transfer is described by a **blocking set** -- the assertions declared
abnormal, hence not carried across.  Circumscribing `ab` is then the preference
for a blocking set that is as small as possible.

Assertions are lifted, not consequences: a context transfers what it *says*,
and the target draws its own conclusions.  Blocking a consequence set would be
ill-behaved anyway, since such a set is closed under equivalence and excluding
`p` while retaining `¬¬p` blocks nothing.

Definitions only -- every theorem about these lives in a separate submission.
-/

import Definitions.Def_TranscendenceTowerContextTheories
import Mathlib.Data.Set.Basic

set_option autoImplicit false

open TranscendenceTower TranscendenceTower.ContextTheories

namespace TranscendenceTower.Lifting

/-- Lift `src` into `tgt`, carrying across every assertion of `src` except
those in the blocking set `A`. -/
def Lift (src tgt A : Set L0) : Set L0 := tgt ∪ (src \ A)

/-- A blocking set is **admissible** when the lifted context is satisfiable.
Declaring assertions abnormal is how a conflict between the two contexts gets
resolved, so the question is which declarations suffice. -/
def Admissible (src tgt A : Set L0) : Prop := ∃ v : Val, Models (Lift src tgt A) v

/-- A **minimal** blocking set: admissible, with no admissible blocking set
strictly smaller.  This is the circumscription of `ab` for a single transfer --
block as little as possible. -/
def MinBlock (src tgt A : Set L0) : Prop :=
  Admissible src tgt A ∧ ∀ B : Set L0, Admissible src tgt B → B ⊆ A → A ⊆ B

end TranscendenceTower.Lifting
