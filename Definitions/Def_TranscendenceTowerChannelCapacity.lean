/-
Definitions for the capacity and repeated-use extension of the finite
route/survival channel.  This imports the immutable information-theory bundle
and adds only the parameterized prior, its induced joint law, and the
memoryless product channel.
-/

import Definitions.Def_TranscendenceTowerInformationTheory

set_option autoImplicit false

open scoped BigOperators
open TranscendenceTower TranscendenceTower.ContextTheories
  TranscendenceTower.Lifting
open TranscendenceTower.InformationTheoryPlatform

namespace TranscendenceTower.InformationTheoryCapacityPlatform

noncomputable section

/-- The input prior for one use: `q` is the probability of the routed input
and `1 - q` is the probability of the direct input. -/
def routedInputPrior (q : ℝ) : Route → ℝ
  | .direct => 1 - q
  | .viaMid => q

/-- The one-use joint route/output law induced by `routedInputPrior` and the
existing route channel. -/
def routedInputJointMass (q : ℝ) (route : Route) (output : Bool) : ℝ :=
  routedInputPrior q route * routeChannel route output

/-- The output marginal obtained from the parameterized one-use joint law. -/
def routedInputOutputMarginal (q : ℝ) (output : Bool) : ℝ :=
  ∑ route : Route, routedInputJointMass q route output

/-- Entropy of the output marginal of the parameterized one-use joint law,
measured in nats. -/
def routedInputOutputEntropy (q : ℝ) : ℝ :=
  finiteEntropy (routedInputOutputMarginal q)

/-- Channel conditional entropy under the parameterized input prior, measured
in nats. -/
def routedInputConditionalEntropy (q : ℝ) : ℝ :=
  ∑ route : Route, routedInputPrior q route * finiteEntropy (routeChannel route)

/-- Closed form for the one-use route/output mutual information in nats.  The
solution proves that the finite mutual-information sum of the explicit joint
law agrees with this expression. -/
def oneUseMutualInformation (q : ℝ) : ℝ :=
  Real.binEntropy (q / 2) - q * Real.log 2

/-- One-use mutual information as the project's finite sum for the
parameterized route/output joint law and its induced marginals. -/
def oneUseJointMutualInformation (q : ℝ) : ℝ :=
  finiteMutualInformation (routedInputJointMass q) (routedInputPrior q)
    (routedInputOutputMarginal q)

/-- The memoryless product channel for `n` independently used route channels.
This gives a probability mass to each output word conditional on an input
word; it is not a code or a coding-theorem assertion. -/
def blockChannel (n : ℕ) (input : Fin n → Route) (output : Fin n → Bool) : ℝ :=
  ∏ i, routeChannel (input i) (output i)

end

end TranscendenceTower.InformationTheoryCapacityPlatform
