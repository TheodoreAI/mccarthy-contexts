/-
Zero-error coding for the finite route/survival channel.

A zero-error code is formulated as a support condition rather than as an
error probability equal to zero: the decoder must be correct on every output
word the codeword can actually produce.  No probability appears in the
definition, only the support of the product channel.

Definitions only; every claim about these objects is proved in the theorem
that imports this bundle.
-/

import Definitions.Def_TranscendenceTowerChannelCapacity

set_option autoImplicit false

open scoped BigOperators
open TranscendenceTower TranscendenceTower.ContextTheories
  TranscendenceTower.Lifting
open TranscendenceTower.InformationTheoryPlatform
open TranscendenceTower.InformationTheoryCapacityPlatform

namespace TranscendenceTower.ZeroErrorPlatform

noncomputable section

/-- `y` is a possible observation when the input word `x` is transmitted:
the product channel assigns it positive mass. -/
def Possible (n : ℕ) (x : Fin n → Route) (y : Fin n → Bool) : Prop :=
  0 < blockChannel n x y

/-- The output word on which every fact survives. -/
def allSurvive (n : ℕ) : Fin n → Bool := fun _ => true

/-- A block code of length `n` carrying `M` messages whose decoder is never
wrong: every output word that can actually arise from codeword `m` is decoded
back to `m`. -/
structure ZeroErrorCode (n M : ℕ) where
  /-- The encoder, sending each message to an input word. -/
  enc : Fin M → (Fin n → Route)
  /-- The decoder, reading an output word back to a message. -/
  dec : (Fin n → Bool) → Fin M
  /-- Correctness on the whole support of each codeword. -/
  correct : ∀ m y, Possible n (enc m) y → dec y = m

/-- Rate of a length-`n`, size-`M` block code, in nats per channel use. -/
def codeRate (n M : ℕ) : ℝ := Real.log M / n

end

end TranscendenceTower.ZeroErrorPlatform
