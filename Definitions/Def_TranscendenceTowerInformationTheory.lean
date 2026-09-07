/-
Finite definitions for the platform-shaped transcendence-tower
information-theory result. The
solution proves the logical classification and every nontrivial probabilistic
claim from these explicit finite models.
-/

import Definitions.Def_TranscendenceTowerLiftConflicts
import Mathlib.Analysis.SpecialFunctions.BinaryEntropy

set_option autoImplicit false

open scoped BigOperators
open TranscendenceTower TranscendenceTower.ContextTheories
  TranscendenceTower.Lifting

namespace TranscendenceTower.InformationTheoryPlatform

noncomputable section

/-- Labels for the two routed minimal-block resolutions. -/
inductive RoutedResolution where
  | dropP
  | dropQ
  deriving DecidableEq

instance : Fintype RoutedResolution where
  elems := {.dropP, .dropQ}
  complete r := by cases r <;> simp

/-- Exchanging the two routed resolutions. -/
def swapResolution : RoutedResolution → RoutedResolution
  | .dropP => .dropQ
  | .dropQ => .dropP

/-- The blocking set selected by each routed-resolution label. -/
def routedBlock : RoutedResolution → Set L0
  | .dropP => {pA}
  | .dropQ => {qA}

/-- The sole direct-resolution label and its empty blocking set. -/
abbrev DirectResolution := Unit

def directBlock (_ : DirectResolution) : Set L0 := ∅

/-- A finite real-valued probability mass function. -/
def IsFiniteDistribution {α : Type} [Fintype α] (mass : α → ℝ) : Prop :=
  (∀ x, 0 ≤ mass x) ∧ ∑ x, mass x = 1

/-- The Shannon summand, in nats. -/
def shannonTerm (mass : ℝ) : ℝ := mass * Real.log mass⁻¹

/-- Shannon entropy of a finite mass function, in nats. -/
def finiteEntropy {α : Type} [Fintype α] (mass : α → ℝ) : ℝ :=
  ∑ x, shannonTerm (mass x)

/-- The singleton mass on the direct-resolution label. -/
def directSingletonMass (_ : DirectResolution) : ℝ := 1

/-- The explicitly imposed fair mass on routed-resolution labels. -/
def uniformRoutedSelectionMass (_ : RoutedResolution) : ℝ := 1 / 2

/-- The direct and routed transfer modes in the finite experiment. -/
inductive Route where
  | direct
  | viaMid
  deriving DecidableEq

instance : Fintype Route where
  elems := {.direct, .viaMid}
  complete r := by cases r <;> simp

/-- The uniform prior on direct and routed transfer. -/
def uniformRoutePrior : Route → ℝ
  | .direct => 1 / 2
  | .viaMid => 1 / 2

/-- `true` denotes survival of the distinguished fact. -/
def routeChannel : Route → Bool → ℝ
  | .direct, true => 1
  | .direct, false => 0
  | .viaMid, true => 1 / 2
  | .viaMid, false => 1 / 2

/-- The explicit four-cell route/output joint law. -/
def jointMass (route : Route) (output : Bool) : ℝ :=
  uniformRoutePrior route * routeChannel route output

/-- Marginals obtained by summing the explicit joint law. -/
def routeMarginal (route : Route) : ℝ := ∑ output : Bool, jointMass route output

def outputMarginal (output : Bool) : ℝ := ∑ route : Route, jointMass route output

/-- Output mass conditional on a route, obtained from the joint law. -/
def routeConditionalMass (route : Route) (output : Bool) : ℝ :=
  jointMass route output / routeMarginal route

/-- Conditional output entropy calculated from the joint law. -/
def uniformRouteConditionalEntropy : ℝ :=
  ∑ route : Route, routeMarginal route * finiteEntropy (routeConditionalMass route)

/-- Entropy of the output marginal derived from the joint law. -/
def uniformRouteOutputEntropy : ℝ := finiteEntropy outputMarginal

/-- Finite mutual information of a joint law and its marginals. -/
def finiteMutualInformation (joint : Route → Bool → ℝ)
    (first : Route → ℝ) (second : Bool → ℝ) : ℝ :=
  ∑ route : Route, ∑ output : Bool,
    if joint route output = 0 then 0 else
      joint route output * Real.log (joint route output / (first route * second output))

/-- Mutual information of the explicit route/output joint law. -/
def uniformRouteMutualInformation : ℝ :=
  finiteMutualInformation jointMass routeMarginal outputMarginal

/-- An abstract binary loss-only channel with survival parameter `s`. -/
def lossChannel (s : ℝ) (input output : Bool) : ℝ :=
  if input then if output then s else 1 - s else if output then 0 else 1

/-- Sequential composition through a freshly sampled intermediate Boolean state. -/
def composeLossChannel (s t : ℝ) (input output : Bool) : ℝ :=
  ∑ middle : Bool, lossChannel s input middle * lossChannel t middle output

/-- Trivial finite-enumeration identities used by the solution. -/
theorem sum_resolutions {M : Type} [AddCommMonoid M] (f : RoutedResolution → M) :
    (∑ r : RoutedResolution, f r) = f .dropP + f .dropQ := by
  change (∑ r ∈ ({.dropP, .dropQ} : Finset RoutedResolution), f r) = _
  simp

theorem sum_routes {M : Type} [AddCommMonoid M] (f : Route → M) :
    (∑ r : Route, f r) = f .direct + f .viaMid := by
  change (∑ r ∈ ({.direct, .viaMid} : Finset Route), f r) = _
  simp

theorem sum_bools {M : Type} [AddCommMonoid M] (f : Bool → M) :
    (∑ b : Bool, f b) = f false + f true := by
  change (∑ b ∈ ({true, false} : Finset Bool), f b) = _
  simp [add_comm]

theorem sum_unit {M : Type} [AddCommMonoid M] (f : Unit → M) :
    (∑ x : Unit, f x) = f () := by
  change (∑ x ∈ ({()} : Finset Unit), f x) = _
  simp

end

end TranscendenceTower.InformationTheoryPlatform
