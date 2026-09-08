import Definitions.Def_TranscendenceTowerChannelCapacity

set_option autoImplicit false

open scoped BigOperators
open TranscendenceTower TranscendenceTower.ContextTheories
  TranscendenceTower.Lifting
open TranscendenceTower.InformationTheoryPlatform
open TranscendenceTower.InformationTheoryCapacityPlatform

namespace TranscendenceTower.VacuityCheck

/-!
Phase-2 vacuity audit for the channel-capacity node.  Every universally
quantified hypothesis class in `theorem solution` is shown non-empty, and the
headline numbers are restated inline so a name cannot silently mean something
weaker.
-/

/-- The `∃!`-parameterization clause quantifies over a NON-EMPTY class:
the optimizing prior is itself a finite distribution. -/
example : IsFiniteDistribution (routedInputPrior (2 / 5)) := by
  constructor
  · intro route; cases route <;> norm_num [routedInputPrior]
  · rw [sum_routes]; norm_num [routedInputPrior]

/-- A second, distinct inhabitant, so the class is not a single point. -/
example : IsFiniteDistribution (routedInputPrior (1 / 2)) := by
  constructor
  · intro route; cases route <;> norm_num [routedInputPrior]
  · rw [sum_routes]; norm_num [routedInputPrior]

/-- The two witnesses really are different priors, so `∃!` has content. -/
example : routedInputPrior (2 / 5) ≠ routedInputPrior (1 / 2) := by
  intro h
  have := congrFun h Route.viaMid
  norm_num [routedInputPrior] at this

/-- The capacity value is a positive real, not a degenerate `0`. -/
example : (0 : ℝ) < Real.log (5 / 4) := Real.log_pos (by norm_num)

/-- The optimizer lies strictly inside the admissible interval, so the
maximum is interior rather than an artefact of the endpoints. -/
example : (0 : ℝ) < 2 / 5 ∧ (2 / 5 : ℝ) < 1 := by norm_num

/-- The endpoints are genuinely worse: the channel carries no information
when the routed input is never used. -/
example : oneUseMutualInformation 0 = 0 := by
  norm_num [oneUseMutualInformation]

/-- `blockChannel` is not the constant-zero function; the product law puts
real mass on the all-survive word. -/
example : blockChannel 1 (fun _ => Route.direct) (fun _ => true) = 1 := by
  norm_num [blockChannel, routeChannel]

end TranscendenceTower.VacuityCheck
