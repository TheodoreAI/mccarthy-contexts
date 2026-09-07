/-
  A finite information-theoretic extension of route-sensitive lifting.

  The logical development supplies exactly two routed minimal blocking sets.
  This module first proves that exhaustiveness result, then imposes a uniform
  law on the resulting subtype.  All Shannon quantities below are finite sums
  over explicitly defined masses, measured in nats.

  The final loss-channel calculation is a separate abstract, memoryless,
  fresh-stage Markov-kernel model for the distinguished fact `p`; it is not a
  general semantics for logical lifting.
-/

import Development.Chaining
import Mathlib.Analysis.SpecialFunctions.BinaryEntropy

set_option autoImplicit false

open scoped BigOperators
open TranscendenceTower TranscendenceTower.ContextTheories
  TranscendenceTower.Lifting

namespace TranscendenceTower.InformationTheory

noncomputable section

/-! ## Actual routed minimal blocks -/

/-- The two names for the two actual minimal resolutions of the routed
transfer. -/
inductive RoutedResolution where
  | dropP
  | dropQ
  deriving DecidableEq, Repr

instance : Fintype RoutedResolution where
  elems := {.dropP, .dropQ}
  complete r := by cases r <;> simp

/-- Exchange the two routed resolutions. -/
def swapResolution : RoutedResolution → RoutedResolution
  | .dropP => .dropQ
  | .dropQ => .dropP

/-- The blocking set named by a routed resolution. -/
def routedBlock : RoutedResolution → Set L0
  | .dropP => {pA}
  | .dropQ => {qA}

/-- The named blocking sets are different. -/
theorem routed_blocks_distinct : routedBlock .dropP ≠ routedBlock .dropQ := by
  intro h
  have hp : pA ∈ routedBlock .dropQ := by
    rw [← h]
    simp [routedBlock]
  have hpq : pA = qA := by
    simpa only [routedBlock, Set.mem_singleton_iff] using hp
  unfold pA qA at hpq
  injection hpq with h01
  exact Nat.zero_ne_one h01

/-- Each named resolution is an actual minimal block of the routed transfer. -/
theorem routedBlock_minimal (r : RoutedResolution) :
    MinBlock srcPQ tgtNand (routedBlock r) := by
  cases r
  · exact Chaining.minblock_singleton' Chaining.admissible_drop_p
  · exact Chaining.minblock_singleton' Chaining.admissible_drop_q

/-- Every admissible routed block must remove `p` or `q`.  This uses the
target's NAND assertion, so irrelevant formulas cannot occur in a minimal
block merely as redundant members. -/
theorem admissible_blocks_p_or_q {A : Set L0} (hA : Admissible srcPQ tgtNand A) :
    pA ∈ A ∨ qA ∈ A := by
  rcases hA with ⟨v, hv⟩
  by_contra h
  push Not at h
  have hp : Form.eval v pA = true :=
    hv pA (Or.inr ⟨Or.inl rfl, h.1⟩)
  have hq : Form.eval v qA = true :=
    hv qA (Or.inr ⟨Or.inr rfl, h.2⟩)
  have hn : Form.eval v (Form.neg (Form.conj pA qA)) = true :=
    hv _ (Or.inl rfl)
  rw [show Form.eval v (Form.neg (Form.conj pA qA))
        = !((Form.eval v pA) && (Form.eval v qA)) from rfl, hp, hq] at hn
  exact absurd hn (by decide)

/-- The exhibited blocks exhaust the actual minimal blocks. -/
theorem minblock_routed_iff (A : Set L0) :
    MinBlock srcPQ tgtNand A ↔ A = {pA} ∨ A = {qA} := by
  constructor
  · intro hA
    rcases admissible_blocks_p_or_q hA.1 with hp | hq
    · left
      have hsmall : ({pA} : Set L0) ⊆ A := by
        intro x hx
        rw [Set.mem_singleton_iff.mp hx]
        exact hp
      exact Set.Subset.antisymm
        (hA.2 {pA} Chaining.admissible_drop_p hsmall) hsmall
    · right
      have hsmall : ({qA} : Set L0) ⊆ A := by
        intro x hx
        rw [Set.mem_singleton_iff.mp hx]
        exact hq
      exact Set.Subset.antisymm
        (hA.2 {qA} Chaining.admissible_drop_q hsmall) hsmall
  · rintro (rfl | rfl)
    · exact Chaining.minblock_singleton' Chaining.admissible_drop_p
    · exact Chaining.minblock_singleton' Chaining.admissible_drop_q

/-- The finite sample space of all, rather than merely exhibited, routed
minimal blocks. -/
abbrev ActualRoutedBlock : Type :=
  {A : Set L0 // MinBlock srcPQ tgtNand A}

/-- A routed-resolution label as the corresponding actual minimal block. -/
def routedResolutionBlock (r : RoutedResolution) : ActualRoutedBlock :=
  ⟨routedBlock r, routedBlock_minimal r⟩

theorem routedResolutionBlock_injective :
    Function.Injective routedResolutionBlock := by
  intro r s h
  have hblocks : routedBlock r = routedBlock s :=
    congrArg Subtype.val h
  cases r <;> cases s
  · rfl
  · exact (routed_blocks_distinct hblocks).elim
  · exact (routed_blocks_distinct hblocks.symm).elim
  · rfl

theorem routedResolutionBlock_surjective :
    Function.Surjective routedResolutionBlock := by
  rintro ⟨A, hA⟩
  rcases (minblock_routed_iff A).mp hA with h | h
  · subst A
    exact ⟨.dropP, rfl⟩
  · subst A
    exact ⟨.dropQ, rfl⟩

/-- The two labels and the subtype of actual routed minimal blocks are
equivalent.  Thus a distribution on either type ranges over exactly the same
formal objects. -/
noncomputable def routedResolutionEquivActualBlock :
    RoutedResolution ≃ ActualRoutedBlock :=
  Equiv.ofBijective routedResolutionBlock
    ⟨routedResolutionBlock_injective, routedResolutionBlock_surjective⟩

noncomputable instance : Fintype ActualRoutedBlock :=
  Fintype.ofEquiv RoutedResolution routedResolutionEquivActualBlock

theorem sum_routed_resolutions {M : Type} [AddCommMonoid M]
    (f : RoutedResolution → M) :
    (∑ r : RoutedResolution, f r) = f .dropP + f .dropQ := by
  change (∑ r ∈ ({.dropP, .dropQ} : Finset RoutedResolution), f r) = _
  simp

/-! ## Finite distributions and routed selection entropy -/

/-- A finite real-valued mass function with the usual nonnegativity and
normalization obligations. -/
def IsFiniteDistribution {α : Type} [Fintype α] (mass : α → ℝ) : Prop :=
  (∀ x, 0 ≤ mass x) ∧ ∑ x, mass x = 1

/-- The finite Shannon summand, with Mathlib's convention `log 0 = 0`. -/
def shannonTerm (mass : ℝ) : ℝ := mass * Real.log mass⁻¹

/-- Shannon entropy of a finite real-valued mass function, in nats. -/
def finiteEntropy {α : Type} [Fintype α] (mass : α → ℝ) : ℝ :=
  ∑ x, shannonTerm (mass x)

/-- A probability policy is a law on the subtype of all actual routed minimal
blocks, not a law on two labels that happen to be examples. -/
structure ResolutionPolicy where
  probability : ActualRoutedBlock → ℝ
  isDistribution : IsFiniteDistribution probability

/-- Read an actual-block policy through the equivalent resolution labels. -/
def ResolutionPolicy.onResolution (π : ResolutionPolicy) :
    RoutedResolution → ℝ :=
  fun r => π.probability (routedResolutionEquivActualBlock r)

theorem ResolutionPolicy.onResolution_nonnegative (π : ResolutionPolicy)
    (r : RoutedResolution) : 0 ≤ π.onResolution r :=
  π.isDistribution.1 _

theorem ResolutionPolicy.onResolution_total (π : ResolutionPolicy) :
    π.onResolution .dropP + π.onResolution .dropQ = 1 := by
  have htotal := π.isDistribution.2
  rw [← Equiv.sum_comp routedResolutionEquivActualBlock π.probability] at htotal
  rw [sum_routed_resolutions] at htotal
  simpa [ResolutionPolicy.onResolution] using htotal

/-- The uniform mass on every actual routed minimal block. -/
def uniformActualRoutedMass (_ : ActualRoutedBlock) : ℝ := 1 / 2

theorem uniformActualRoutedMass_is_distribution :
    IsFiniteDistribution uniformActualRoutedMass := by
  constructor
  · intro A
    norm_num [uniformActualRoutedMass]
  · rw [← Equiv.sum_comp routedResolutionEquivActualBlock uniformActualRoutedMass]
    rw [sum_routed_resolutions]
    norm_num [uniformActualRoutedMass]

/-- The explicitly imposed fair policy on all actual routed blocks. -/
def symmetricRoutedPolicy : ResolutionPolicy :=
  ⟨uniformActualRoutedMass, uniformActualRoutedMass_is_distribution⟩

/-- A policy is symmetric when exchanging the two actual alternatives changes
no mass. -/
def ResolutionPolicy.Symmetric (π : ResolutionPolicy) : Prop :=
  ∀ r, π.onResolution r = π.onResolution (swapResolution r)

theorem symmetricRoutedPolicy_is_symmetric :
    symmetricRoutedPolicy.Symmetric := by
  intro r
  cases r <;> norm_num [ResolutionPolicy.onResolution, symmetricRoutedPolicy,
    uniformActualRoutedMass, swapResolution]

/-- Symmetry and normalization force one half on each actual routed block. -/
theorem symmetric_policy_is_fair (π : ResolutionPolicy)
    (hπ : π.Symmetric) :
    π.onResolution .dropP = 1 / 2 ∧ π.onResolution .dropQ = 1 / 2 := by
  have hswap := hπ .dropP
  change π.onResolution .dropP = π.onResolution .dropQ at hswap
  constructor <;> linarith [π.onResolution_total, hswap]

/-- Entropy of the imposed routed-selection policy. -/
def selectionEntropy (π : ResolutionPolicy) : ℝ := finiteEntropy π.probability

/-- A fair selection between all actual routed minimal blocks has `log 2` nats
of Shannon entropy. -/
theorem symmetric_routed_selection_entropy :
    selectionEntropy symmetricRoutedPolicy = Real.log 2 := by
  unfold selectionEntropy finiteEntropy
  rw [← Equiv.sum_comp routedResolutionEquivActualBlock
    (fun A => shannonTerm (symmetricRoutedPolicy.probability A))]
  rw [sum_routed_resolutions]
  norm_num [symmetricRoutedPolicy, uniformActualRoutedMass, shannonTerm]
  ring

/-- The unique actual direct minimal block. -/
abbrev ActualDirectBlock : Type :=
  {A : Set L0 // MinBlock srcP tgtNand A}

/-- The direct transfer's empty blocking set, as an actual minimal block. -/
def directMinimalBlock : ActualDirectBlock :=
  ⟨∅, Chaining.minblock_direct⟩

theorem direct_minimal_block_is_empty (A : Set L0) (hA : MinBlock srcP tgtNand A) :
    A = ∅ := Chaining.minblock_direct_unique hA

noncomputable def directBlockEquiv : Unit ≃ ActualDirectBlock where
  toFun _ := directMinimalBlock
  invFun _ := ()
  left_inv _ := rfl
  right_inv A := by
    apply Subtype.ext
    exact (direct_minimal_block_is_empty A.1 A.2).symm

noncomputable instance : Fintype ActualDirectBlock :=
  Fintype.ofEquiv Unit directBlockEquiv

theorem sum_unit {M : Type} [AddCommMonoid M] (f : Unit → M) :
    (∑ x : Unit, f x) = f () := by
  change (∑ x ∈ ({()} : Finset Unit), f x) = _
  simp

/-- The Dirac distribution on the actual unique direct minimal block. -/
def directDirac (A : ActualDirectBlock) : ℝ :=
  if A = directMinimalBlock then 1 else 0

theorem directDirac_is_distribution : IsFiniteDistribution directDirac := by
  constructor
  · intro A
    by_cases h : A = directMinimalBlock <;> simp [directDirac, h]
  · rw [← Equiv.sum_comp directBlockEquiv directDirac]
    rw [sum_unit]
    simp [directBlockEquiv, directDirac]

/-- Direct selection entropy is the entropy of this singleton Dirac law. -/
def directSelectionEntropy : ℝ := finiteEntropy directDirac

theorem direct_selection_entropy : directSelectionEntropy = 0 := by
  unfold directSelectionEntropy finiteEntropy
  rw [← Equiv.sum_comp directBlockEquiv (fun A => shannonTerm (directDirac A))]
  rw [sum_unit]
  simp [directBlockEquiv, directDirac, shannonTerm]

/-- Backwards-compatible name for the entropy derived from the direct Dirac
law. -/
def forcedDirectSelectionEntropy : ℝ := directSelectionEntropy

theorem forced_direct_selection_entropy : forcedDirectSelectionEntropy = 0 :=
  direct_selection_entropy

/-! ## Route/output joint law -/

/-- The two routes in the finite experiment. -/
inductive Route where
  | direct
  | viaMid
  deriving DecidableEq, Repr

instance : Fintype Route where
  elems := {.direct, .viaMid}
  complete r := by cases r <;> simp

theorem sum_routes {M : Type} [AddCommMonoid M] (f : Route → M) :
    (∑ r : Route, f r) = f .direct + f .viaMid := by
  change (∑ r ∈ ({.direct, .viaMid} : Finset Route), f r) = _
  simp

theorem sum_bools {M : Type} [AddCommMonoid M] (f : Bool → M) :
    (∑ b : Bool, f b) = f false + f true := by
  change (∑ b ∈ ({true, false} : Finset Bool), f b) = _
  simp [add_comm]

/-- A distribution over Boolean survival outputs.  `true` means `p` survives. -/
abbrev IsDistribution (row : Bool → ℝ) : Prop := IsFiniteDistribution row

/-- A loss-only binary channel.  This is an abstract memoryless model: it does
not assert that false logical inputs model arbitrary lifting behavior. -/
def lossChannel (s : ℝ) (input output : Bool) : ℝ :=
  if input then if output then s else 1 - s else if output then 0 else 1

theorem lossChannel_row_is_distribution (s : ℝ) (hs0 : 0 ≤ s) (hs1 : s ≤ 1)
    (input : Bool) : IsDistribution (lossChannel s input) := by
  constructor
  · intro output
    cases input <;> cases output <;> simp [lossChannel] <;> linarith
  · cases input <;> simp [lossChannel]

/-- The logically supported route model has only a route input and a survival
output.  It records the direct certainty and the fair actual-block policy; it
does not treat logical lifting as a two-input Boolean channel. -/
def routeChannel : Route → Bool → ℝ
  | .direct, true => 1
  | .direct, false => 0
  | .viaMid, true => 1 / 2
  | .viaMid, false => 1 / 2

theorem routeChannel_is_distribution (r : Route) : IsDistribution (routeChannel r) := by
  cases r with
  | direct =>
      constructor
      · intro output
        cases output <;> norm_num [routeChannel]
      · rw [sum_bools]
        norm_num [routeChannel]
  | viaMid =>
      constructor
      · intro output
        cases output <;> norm_num [routeChannel]
      · rw [sum_bools]
        norm_num [routeChannel]

/-- The semantic fact behind the direct output row. -/
theorem p_survives_on_direct_route (A : Set L0) (hA : MinBlock srcP tgtNand A) :
    pA ∈ Cn (Lift srcP tgtNand A) :=
  Chaining.p_survives_every_direct A hA

theorem direct_route_transition_probabilities :
    routeChannel .direct true = 1 ∧ routeChannel .direct false = 0 := by
  constructor <;> norm_num [routeChannel]

theorem routed_symmetric_transition_probabilities :
    routeChannel .viaMid true = 1 / 2 ∧ routeChannel .viaMid false = 1 / 2 := by
  constructor <;> norm_num [routeChannel]

/-- The survival mass of the actual-block policy agrees with the routed output
row. -/
theorem routed_channel_matches_policy :
    routeChannel .viaMid true =
      symmetricRoutedPolicy.onResolution .dropQ := by
  rw [symmetric_policy_is_fair symmetricRoutedPolicy
    symmetricRoutedPolicy_is_symmetric |>.2]
  exact routed_symmetric_transition_probabilities.1

/-- The uniform prior on direct and routed transfer. -/
def uniformRoutePrior : Route → ℝ
  | .direct => 1 / 2
  | .viaMid => 1 / 2

theorem uniformRoutePrior_is_distribution :
    IsFiniteDistribution uniformRoutePrior := by
  constructor
  · intro r
    cases r <;> norm_num [uniformRoutePrior]
  · rw [sum_routes]
    norm_num [uniformRoutePrior]

/-- The explicit four-cell joint mass for uniformly selecting a route and then
observing its survival output. -/
def routeOutputJointMass (r : Route) (output : Bool) : ℝ :=
  uniformRoutePrior r * routeChannel r output

theorem routeOutputJointMass_nonnegative (r : Route) (output : Bool) :
    0 ≤ routeOutputJointMass r output := by
  cases r <;> cases output <;> norm_num [routeOutputJointMass,
    uniformRoutePrior, routeChannel]

theorem routeOutputJointMass_normalized :
    ∑ r : Route, ∑ output : Bool, routeOutputJointMass r output = 1 := by
  rw [sum_routes]
  simp_rw [sum_bools]
  norm_num [routeOutputJointMass, uniformRoutePrior, routeChannel]

theorem routeOutputJointMass_is_distribution :
    IsFiniteDistribution (fun x : Route × Bool => routeOutputJointMass x.1 x.2) := by
  constructor
  · rintro ⟨r, output⟩
    exact routeOutputJointMass_nonnegative r output
  · rw [Fintype.sum_prod_type]
    exact routeOutputJointMass_normalized

/-- Marginal route mass derived by summing the explicit joint law. -/
def routeMarginal (r : Route) : ℝ := ∑ output : Bool, routeOutputJointMass r output

/-- Marginal survival-output mass derived by summing the explicit joint law. -/
def outputMarginal (output : Bool) : ℝ := ∑ r : Route, routeOutputJointMass r output

theorem routeMarginal_eq_prior (r : Route) :
    routeMarginal r = uniformRoutePrior r := by
  cases r <;> rw [routeMarginal, sum_bools] <;>
    norm_num [routeOutputJointMass, uniformRoutePrior, routeChannel]

theorem routeMarginal_is_distribution : IsFiniteDistribution routeMarginal := by
  constructor
  · intro r
    rw [routeMarginal_eq_prior r]
    exact uniformRoutePrior_is_distribution.1 r
  · simp_rw [routeMarginal_eq_prior]
    exact uniformRoutePrior_is_distribution.2

theorem outputMarginal_false : outputMarginal false = 1 / 4 := by
  rw [outputMarginal, sum_routes]
  norm_num [outputMarginal, routeOutputJointMass, uniformRoutePrior, routeChannel]

theorem outputMarginal_true : outputMarginal true = 3 / 4 := by
  rw [outputMarginal, sum_routes]
  norm_num [outputMarginal, routeOutputJointMass, uniformRoutePrior, routeChannel]

theorem outputMarginal_is_distribution : IsDistribution outputMarginal := by
  constructor
  · intro output
    cases output
    · rw [outputMarginal_false]
      norm_num
    · rw [outputMarginal_true]
      norm_num
  · rw [sum_bools, outputMarginal_false, outputMarginal_true]
    norm_num

/-- The old output spelling, now definitionally the joint law's marginal. -/
def uniformRouteOutput : Bool → ℝ := outputMarginal

theorem uniform_route_survival_probability : uniformRouteOutput true = 3 / 4 :=
  outputMarginal_true

/-- The conditional entropy calculated directly from the joint law and its
route marginal. -/
def jointConditionalEntropy (joint : Route → Bool → ℝ) (first : Route → ℝ) : ℝ :=
  ∑ r : Route, first r * finiteEntropy (fun output => joint r output / first r)

/-- The route-conditioned output mass, obtained by dividing the joint law by
its positive route marginal. -/
def routeConditionalMass (r : Route) (output : Bool) : ℝ :=
  routeOutputJointMass r output / routeMarginal r

theorem routeConditionalMass_is_distribution (r : Route) :
    IsDistribution (routeConditionalMass r) := by
  unfold routeConditionalMass
  rw [routeMarginal_eq_prior r]
  cases r with
  | direct =>
      constructor
      · intro output
        cases output <;> norm_num [routeOutputJointMass, uniformRoutePrior,
          routeChannel]
      · rw [sum_bools]
        norm_num [routeOutputJointMass, uniformRoutePrior, routeChannel]
  | viaMid =>
      constructor
      · intro output
        cases output <;> norm_num [routeOutputJointMass, uniformRoutePrior,
          routeChannel]
      · rw [sum_bools]
        norm_num [routeOutputJointMass, uniformRoutePrior, routeChannel]

def uniformRouteConditionalEntropy : ℝ :=
  ∑ r : Route, routeMarginal r * finiteEntropy (routeConditionalMass r)

theorem uniform_route_conditional_entropy :
    uniformRouteConditionalEntropy = Real.log 2 / 2 := by
  unfold uniformRouteConditionalEntropy finiteEntropy routeConditionalMass
  simp_rw [sum_routes, sum_bools]
  norm_num [routeMarginal, routeOutputJointMass, uniformRoutePrior, routeChannel,
    shannonTerm]
  ring

/-- The entropy of the survival-output marginal obtained from the joint law. -/
def uniformRouteOutputEntropy : ℝ := finiteEntropy outputMarginal

theorem uniform_route_output_entropy :
    uniformRouteOutputEntropy = Real.binEntropy (3 / 4) := by
  unfold uniformRouteOutputEntropy finiteEntropy
  rw [sum_bools, outputMarginal_false, outputMarginal_true]
  norm_num [shannonTerm, Real.binEntropy]
  ring

/-- Finite mutual information as the expected pointwise mutual information of
an explicit joint law and its two marginals.  Zero-mass cells contribute zero. -/
def finiteMutualInformation (joint : Route → Bool → ℝ)
    (first : Route → ℝ) (second : Bool → ℝ) : ℝ :=
  ∑ r : Route, ∑ output : Bool,
    if joint r output = 0 then 0 else
      joint r output * Real.log (joint r output / (first r * second output))

/-- Mutual information of the explicit route/output joint law. -/
def uniformRouteMutualInformation : ℝ :=
  finiteMutualInformation routeOutputJointMass routeMarginal outputMarginal

private theorem log_four_eq_two_log_two :
    Real.log 4 = 2 * Real.log 2 := by
  have h := Real.log_mul (show (2 : ℝ) ≠ 0 by norm_num)
    (show (2 : ℝ) ≠ 0 by norm_num)
  norm_num at h ⊢
  linarith

private theorem log_two_thirds :
    Real.log (2 / 3 : ℝ) = Real.log (4 / 3 : ℝ) - Real.log 2 := by
  rw [Real.log_div (by norm_num) (by norm_num),
    Real.log_div (by norm_num) (by norm_num), log_four_eq_two_log_two]
  ring

/-- The standard entropy-difference expression is derived from, rather than
used to define, the finite joint-law mutual information. -/
theorem uniform_route_mutual_information_from_joint :
    uniformRouteMutualInformation =
      uniformRouteOutputEntropy - uniformRouteConditionalEntropy := by
  unfold uniformRouteMutualInformation finiteMutualInformation
    uniformRouteOutputEntropy uniformRouteConditionalEntropy finiteEntropy
    routeConditionalMass routeMarginal outputMarginal routeOutputJointMass
    uniformRoutePrior routeChannel shannonTerm
  simp_rw [sum_routes, sum_bools]
  norm_num
  rw [log_two_thirds, log_four_eq_two_log_two]
  ring

theorem uniform_route_mutual_information :
    uniformRouteMutualInformation =
      Real.binEntropy (3 / 4) - Real.log 2 / 2 := by
  rw [uniform_route_mutual_information_from_joint, uniform_route_output_entropy,
    uniform_route_conditional_entropy]

/-! ## Abstract fresh-stage loss kernels -/

/-- Sequential composition of two abstract loss kernels, summing over a fresh
intermediate Boolean state. -/
def composeLossChannel (s t : ℝ) (input output : Bool) : ℝ :=
  ∑ middle : Bool, lossChannel s input middle * lossChannel t middle output

/-- This unrestricted equality is algebraic only.  Its probabilistic
interpretation requires the fresh-stage Markov-kernel hypotheses below. -/
theorem lossChannel_compose_algebraic (s t : ℝ) (input output : Bool) :
    composeLossChannel s t input output = lossChannel (s * t) input output := by
  cases input <;> cases output <;>
    (simp [composeLossChannel, lossChannel] <;> ring)

/-- Under unit-interval survival parameters, the composed fresh-stage kernel
has valid probability rows. -/
theorem fresh_stage_composite_row_is_distribution (s t : ℝ)
    (hs0 : 0 ≤ s) (hs1 : s ≤ 1) (ht0 : 0 ≤ t) (ht1 : t ≤ 1)
    (input : Bool) : IsDistribution (composeLossChannel s t input) := by
  have hcompose : composeLossChannel s t input = lossChannel (s * t) input := by
    funext output
    exact lossChannel_compose_algebraic s t input output
  rw [hcompose]
  apply lossChannel_row_is_distribution
  · exact mul_nonneg hs0 ht0
  · calc
      s * t ≤ 1 * t := mul_le_mul_of_nonneg_right hs1 ht0
      _ ≤ 1 * 1 := mul_le_mul_of_nonneg_left ht1 (by norm_num)
      _ = 1 := by norm_num

/-- Fresh-stage Markov-kernel composition: provided both rows are probability
kernels, summing over a newly sampled intermediate state yields the kernel
with survival parameter `s * t`. -/
theorem fresh_stage_lossChannel_compose (s t : ℝ)
    (hs0 : 0 ≤ s) (hs1 : s ≤ 1) (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    composeLossChannel s t = lossChannel (s * t)
      ∧ ∀ input, IsDistribution (composeLossChannel s t input) := by
  constructor
  · funext input output
    exact lossChannel_compose_algebraic s t input output
  · exact fresh_stage_composite_row_is_distribution s t hs0 hs1 ht0 ht1

/-- A deterministic direct fresh stage followed by a fair fresh routed stage
survives with probability one half. -/
theorem direct_then_routed_fresh_stage_survival :
    composeLossChannel 1 (1 / 2) true true = 1 / 2 := by
  have hkernel := fresh_stage_lossChannel_compose 1 (1 / 2)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  rw [show composeLossChannel 1 (1 / 2) true true =
      lossChannel (1 * (1 / 2)) true true by
        exact congrFun (congrFun hkernel.1 true) true]
  norm_num [lossChannel]

/-- Two fair fresh routed stages survive with probability one quarter.  This is
a property of the memoryless fresh-stage kernel model, not a conclusion from
one-stage logical marginals alone. -/
theorem two_routed_fresh_stages_survival :
    composeLossChannel (1 / 2) (1 / 2) true true = 1 / 4 := by
  have hkernel := fresh_stage_lossChannel_compose (1 / 2) (1 / 2)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  rw [show composeLossChannel (1 / 2) (1 / 2) true true =
      lossChannel ((1 / 2) * (1 / 2)) true true by
        exact congrFun (congrFun hkernel.1 true) true]
  norm_num [lossChannel]

/-! ## Headline checks -/

example : directSelectionEntropy = 0 := direct_selection_entropy

example : selectionEntropy symmetricRoutedPolicy = Real.log 2 :=
  symmetric_routed_selection_entropy

example : uniformRouteOutput true = 3 / 4 :=
  uniform_route_survival_probability

example : uniformRouteConditionalEntropy = Real.log 2 / 2 :=
  uniform_route_conditional_entropy

example : uniformRouteMutualInformation =
    Real.binEntropy (3 / 4) - Real.log 2 / 2 :=
  uniform_route_mutual_information

example : composeLossChannel (1 / 2) (1 / 2) true true = 1 / 4 :=
  two_routed_fresh_stages_survival

section Verification

#print axioms minblock_routed_iff
#print axioms routedResolutionEquivActualBlock
#print axioms uniformActualRoutedMass_is_distribution
#print axioms symmetric_routed_selection_entropy
#print axioms direct_selection_entropy
#print axioms routeOutputJointMass_is_distribution
#print axioms routeMarginal_eq_prior
#print axioms outputMarginal_false
#print axioms outputMarginal_true
#print axioms uniform_route_conditional_entropy
#print axioms uniform_route_mutual_information_from_joint
#print axioms uniform_route_mutual_information
#print axioms fresh_stage_composite_row_is_distribution
#print axioms fresh_stage_lossChannel_compose
#print axioms two_routed_fresh_stages_survival

end Verification

end

end TranscendenceTower.InformationTheory
