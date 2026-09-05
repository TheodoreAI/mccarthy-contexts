/-
Measuring how much freedom a relaxed transcendence context retains.

A relaxed tower is underdetermined: dropping even one instance of the
transcendence schema admits more than one transcending context.  A logic of
relaxing contexts must therefore say which of the survivors is intended.  These
definitions provide the apparatus for asking that question precisely: the set of
assumptions at which a context departs from the one below, the class of contexts
obeying the schema outside a given relaxation set, and the canonical context
that changes nothing.

Definitions only -- every theorem about these lives in a separate submission.
-/

import Definitions.Def_TranscendenceTowerRelaxation
import Mathlib.Data.Set.Basic

set_option autoImplicit false

open TranscendenceTower TranscendenceTower.Relaxation

namespace TranscendenceTower.MinimalChange

/-- The **change set** of a transcending context: the assumptions at which it
departs from the context below. -/
def Delta (v : Atom 0 → Bool) (N : Atom 1 → Bool) : Set (Lang 0) :=
  {p | N (Sum.inr p) ≠ Form.eval v p}

/-- The **`A`-relaxed models**: contexts extending `v` that obey the
transcendence schema everywhere outside the relaxation set `A`. -/
def Mod (v : Atom 0 → Bool) (A : Set (Lang 0)) : Set (Atom 1 → Bool) :=
  {N | ExtendsBase v N ∧ ∀ p : Lang 0, p ∉ A → Form.eval N (schema p) = true}

/-- The canonical **copy context**, which carries every truth value upward
unchanged.  This is the transcending context of the unrelaxed tower. -/
def copy (v : Atom 0 → Bool) : Atom 1 → Bool := mk1 v (fun p => Form.eval v p)

end TranscendenceTower.MinimalChange
