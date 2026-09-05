/-
Contexts as theories, with circumscription.

Modelling a context as a *valuation* makes relaxation rigid: the set of places
where a transcending context departs from the one below parametrises the
possibilities exactly, and the minimal-change reading always returns the context
that changes nothing.  The rigidity traces to truth values being Boolean, so
knowing where a context differs determines what it says there.

These definitions change the setting.  A context is a *theory* -- a set of
sentences -- and "true in the context" means derivable from it.  Relaxing an
assumption now removes a sentence, altering a whole consequence set rather than
flipping one bit.

Classical consequence is monotone, so on its own this change would leave
relaxation unable to create conclusions.  Also defined here is the nonmonotonic
apparatus McCarthy introduced for precisely this purpose: an abnormality set, the
models of a theory that minimise it, and the consequence relation they induce --
circumscription.

Definitions only -- every theorem about these lives in a separate submission.
-/

import Definitions.Def_TranscendenceTowerCore
import Mathlib.Data.Set.Basic

set_option autoImplicit false

open TranscendenceTower

namespace TranscendenceTower.ContextTheories

/-- Sentences of the base language. -/
abbrev L0 : Type := Form Base

/-- A valuation of the base language. -/
abbrev Val : Type := Base → Bool

/-- `v` is a model of the theory `T`. -/
def Models (T : Set L0) (v : Val) : Prop := ∀ p ∈ T, Form.eval v p = true

/-- Classical consequence: what holds in every model of `T`.  This is the
reading of "true in the context `T`" appropriate to contexts-as-theories. -/
def Cn (T : Set L0) : Set L0 := {p | ∀ v : Val, Models T v → Form.eval v p = true}

/-- The abnormal atoms made true by `v`, relative to a designated set `ab` of
abnormality atoms. -/
def AbSet (ab : Set Base) (v : Val) : Set Base := {k | k ∈ ab ∧ v k = true}

/-- `v` models `T` while minimising abnormality: no model of `T` is strictly
more normal.  This is circumscription, stated as minimality of the extension of
the abnormality predicate. -/
def MinModel (ab : Set Base) (T : Set L0) (v : Val) : Prop :=
  Models T v ∧ ∀ w : Val, Models T w → AbSet ab w ⊆ AbSet ab v → AbSet ab v ⊆ AbSet ab w

/-- Circumscriptive consequence: what holds in every minimal model. -/
def CnCirc (ab : Set Base) (T : Set L0) : Set L0 :=
  {p | ∀ v : Val, MinModel ab T v → Form.eval v p = true}

end TranscendenceTower.ContextTheories
