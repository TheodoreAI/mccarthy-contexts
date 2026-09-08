import Definitions.Def_TranscendenceTowerChannelCapacity

set_option autoImplicit false

open scoped BigOperators
open TranscendenceTower TranscendenceTower.ContextTheories
  TranscendenceTower.Lifting
open TranscendenceTower.InformationTheoryPlatform
open TranscendenceTower.InformationTheoryCapacityPlatform

private theorem capacity_routeChannel_is_distribution (route : Route) :
    IsFiniteDistribution (routeChannel route) := by
  cases route with
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

private theorem capacity_prior_is_distribution {q : ℝ} (hq0 : 0 ≤ q)
    (hq1 : q ≤ 1) : IsFiniteDistribution (routedInputPrior q) := by
  constructor
  · intro route
    cases route <;> simp [routedInputPrior] <;> linarith
  · rw [sum_routes]
    simp [routedInputPrior]

private theorem capacity_every_prior_is_parameterized (prior : Route → ℝ)
    (hprior : IsFiniteDistribution prior) :
    ∃! q : ℝ, 0 ≤ q ∧ q ≤ 1 ∧ prior = routedInputPrior q := by
  refine ⟨prior .viaMid, ?_, ?_⟩
  · have hsum := hprior.2
    rw [sum_routes] at hsum
    refine ⟨hprior.1 .viaMid, ?_, ?_⟩
    · linarith [hprior.1 .direct]
    · funext route
      cases route with
      | direct =>
          simp [routedInputPrior]
          linarith
      | viaMid => rfl
  · intro q hq
    simpa [routedInputPrior] using (congrFun hq.2.2 Route.viaMid).symm

private theorem capacity_joint_is_distribution {q : ℝ} (hq0 : 0 ≤ q)
    (hq1 : q ≤ 1) :
    IsFiniteDistribution (fun x : Route × Bool => routedInputJointMass q x.1 x.2) := by
  constructor
  · rintro ⟨route, output⟩
    exact mul_nonneg ((capacity_prior_is_distribution hq0 hq1).1 route)
      ((capacity_routeChannel_is_distribution route).1 output)
  · rw [Fintype.sum_prod_type, sum_routes]
    simp_rw [sum_bools]
    norm_num [routedInputJointMass, routedInputPrior, routeChannel]
    ring

private theorem capacity_output_marginal_false (q : ℝ) :
    routedInputOutputMarginal q false = q / 2 := by
  rw [routedInputOutputMarginal, sum_routes]
  norm_num [routedInputJointMass, routedInputPrior, routeChannel]
  ring

private theorem capacity_output_marginal_true (q : ℝ) :
    routedInputOutputMarginal q true = 1 - q / 2 := by
  rw [routedInputOutputMarginal, sum_routes]
  norm_num [routedInputJointMass, routedInputPrior, routeChannel]
  ring

private theorem capacity_output_entropy (q : ℝ) :
    routedInputOutputEntropy q = Real.binEntropy (q / 2) := by
  unfold routedInputOutputEntropy finiteEntropy
  rw [sum_bools, capacity_output_marginal_false, capacity_output_marginal_true]
  simp [shannonTerm, Real.binEntropy]

private theorem capacity_conditional_entropy (q : ℝ) :
    routedInputConditionalEntropy q = q * Real.log 2 := by
  have hdirect : finiteEntropy (routeChannel .direct) = 0 := by
    unfold finiteEntropy
    rw [sum_bools]
    norm_num [routeChannel, shannonTerm]
  have hvia : finiteEntropy (routeChannel .viaMid) = Real.log 2 := by
    unfold finiteEntropy
    rw [sum_bools]
    norm_num [routeChannel, shannonTerm]
    ring
  unfold routedInputConditionalEntropy
  rw [sum_routes, hdirect, hvia]
  simp [routedInputPrior]

private theorem capacity_information_from_joint (q : ℝ) :
    oneUseMutualInformation q =
      routedInputOutputEntropy q - routedInputConditionalEntropy q := by
  rw [capacity_output_entropy, capacity_conditional_entropy]
  rfl

private theorem capacity_joint_information_eq_closed_form (q : ℝ)
    (hq0 : 0 ≤ q) (hq1 : q ≤ 1) :
    oneUseJointMutualInformation q = oneUseMutualInformation q := by
  rcases eq_or_lt_of_le hq0 with rfl | hqpos
  · unfold oneUseJointMutualInformation finiteMutualInformation
    simp_rw [routedInputOutputMarginal, sum_routes, sum_bools]
    norm_num [routedInputJointMass, routedInputPrior, routeChannel,
      oneUseMutualInformation, Real.binEntropy]
  rcases eq_or_lt_of_le hq1 with rfl | hqlt
  · unfold oneUseJointMutualInformation finiteMutualInformation
    simp_rw [routedInputOutputMarginal, sum_routes, sum_bools]
    norm_num [routedInputJointMass, routedInputPrior, routeChannel,
      oneUseMutualInformation, Real.binEntropy]
    ring
  have hqne : q ≠ 0 := ne_of_gt hqpos
  have hsubne : 1 - q ≠ 0 := ne_of_gt (sub_pos.mpr hqlt)
  have hmargpos : 0 < 1 - q / 2 := by nlinarith
  have hmargne : 1 - q / 2 ≠ 0 := ne_of_gt hmargpos
  have hsum : 1 - q + q * 2⁻¹ = 1 - q / 2 := by norm_num; ring
  have hdirect : (1 - q) / ((1 - q) * (1 - q / 2)) = 1 / (1 - q / 2) := by
    field_simp
  have hfalse : q * 2⁻¹ / (q * (q * 2⁻¹)) = 1 / q := by
    field_simp
  have htrue : q * 2⁻¹ / (q * (1 - q / 2)) = 1 / (2 * (1 - q / 2)) := by
    field_simp
  unfold oneUseJointMutualInformation finiteMutualInformation
  simp_rw [routedInputOutputMarginal, sum_routes, sum_bools]
  simp [routedInputJointMass, routedInputPrior, routeChannel,
    oneUseMutualInformation, Real.binEntropy, hqne, hsubne]
  rw [hsum, hdirect, hfalse, htrue]
  simp only [one_div]
  rw [Real.log_inv, Real.log_inv, Real.log_inv,
    Real.log_mul (by norm_num : (2 : ℝ) ≠ 0) hmargne,
    Real.log_div (by norm_num : (2 : ℝ) ≠ 0) hqne]
  ring

private theorem capacity_log_four_eq_two_log_two :
    Real.log 4 = 2 * Real.log 2 := by
  have h := Real.log_mul (show (2 : ℝ) ≠ 0 by norm_num)
    (show (2 : ℝ) ≠ 0 by norm_num)
  norm_num at h ⊢
  linarith

private theorem capacity_information_as_qaryEntropy (q : ℝ) :
    oneUseMutualInformation q =
      Real.qaryEntropy 5 (1 - q / 2) - Real.log 4 := by
  unfold oneUseMutualInformation Real.qaryEntropy
  norm_num
  rw [capacity_log_four_eq_two_log_two]
  ring

private theorem capacity_information_at_two_fifths :
    oneUseMutualInformation (2 / 5) = Real.log (5 / 4) := by
  unfold oneUseMutualInformation Real.binEntropy
  norm_num
  rw [Real.log_div (by norm_num) (by norm_num), capacity_log_four_eq_two_log_two]
  ring

private theorem capacity_information_lt {q : ℝ} (hq0 : 0 ≤ q) (hq1 : q ≤ 1)
    (hq : q ≠ 2 / 5) : oneUseMutualInformation q < Real.log (5 / 4) := by
  by_cases hlt : q < 2 / 5
  · have hy : 1 - q / 2 ∈ Set.Icc (1 - 1 / (5 : ℝ)) 1 := by
      constructor <;> nlinarith
    have hopt : 1 - (2 / 5 : ℝ) / 2 ∈ Set.Icc (1 - 1 / (5 : ℝ)) 1 := by
      norm_num
    have hyopt : 1 - (2 / 5 : ℝ) / 2 < 1 - q / 2 := by
      linarith
    have hstrict : Real.qaryEntropy 5 (1 - q / 2) <
        Real.qaryEntropy 5 (1 - (2 / 5 : ℝ) / 2) :=
      Real.qaryEntropy_strictAntiOn (by norm_num) hopt hy hyopt
    calc
      oneUseMutualInformation q =
          Real.qaryEntropy 5 (1 - q / 2) - Real.log 4 :=
        capacity_information_as_qaryEntropy q
      _ < Real.qaryEntropy 5 (1 - (2 / 5 : ℝ) / 2) - Real.log 4 :=
        sub_lt_sub_right hstrict _
      _ = oneUseMutualInformation (2 / 5) :=
        (capacity_information_as_qaryEntropy _).symm
      _ = Real.log (5 / 4) := capacity_information_at_two_fifths
  · have hgt : 2 / 5 < q :=
      lt_of_le_of_ne (le_of_not_gt hlt) (Ne.symm hq)
    have hy : 1 - q / 2 ∈ Set.Icc 0 (1 - 1 / (5 : ℝ)) := by
      constructor <;> nlinarith
    have hopt : 1 - (2 / 5 : ℝ) / 2 ∈ Set.Icc 0 (1 - 1 / (5 : ℝ)) := by
      norm_num
    have hyopt : 1 - q / 2 < 1 - (2 / 5 : ℝ) / 2 := by
      linarith
    have hstrict : Real.qaryEntropy 5 (1 - q / 2) <
        Real.qaryEntropy 5 (1 - (2 / 5 : ℝ) / 2) :=
      Real.qaryEntropy_strictMonoOn (by norm_num) hy hopt hyopt
    calc
      oneUseMutualInformation q =
          Real.qaryEntropy 5 (1 - q / 2) - Real.log 4 :=
        capacity_information_as_qaryEntropy q
      _ < Real.qaryEntropy 5 (1 - (2 / 5 : ℝ) / 2) - Real.log 4 :=
        sub_lt_sub_right hstrict _
      _ = oneUseMutualInformation (2 / 5) :=
        (capacity_information_as_qaryEntropy _).symm
      _ = Real.log (5 / 4) := capacity_information_at_two_fifths

private theorem capacity_information_bound (q : ℝ) (hq0 : 0 ≤ q) (hq1 : q ≤ 1) :
    oneUseMutualInformation q ≤ Real.log (5 / 4) := by
  by_cases hq : q = 2 / 5
  · subst q
    exact le_of_eq capacity_information_at_two_fifths
  · exact (capacity_information_lt hq0 hq1 hq).le

private theorem capacity_information_eq_iff (q : ℝ) (hq0 : 0 ≤ q) (hq1 : q ≤ 1) :
    oneUseMutualInformation q = Real.log (5 / 4) ↔ q = 2 / 5 := by
  constructor
  · intro hq
    by_contra hne
    have hlt := capacity_information_lt hq0 hq1 hne
    linarith
  · intro hq
    subst q
    exact capacity_information_at_two_fifths

private theorem capacity_joint_information_at_two_fifths :
    oneUseJointMutualInformation (2 / 5) = Real.log (5 / 4) := by
  rw [capacity_joint_information_eq_closed_form (2 / 5) (by norm_num)
    (by norm_num)]
  exact capacity_information_at_two_fifths

private theorem capacity_joint_information_bound (q : ℝ) (hq0 : 0 ≤ q)
    (hq1 : q ≤ 1) :
    oneUseJointMutualInformation q ≤ Real.log (5 / 4) := by
  rw [capacity_joint_information_eq_closed_form q hq0 hq1]
  exact capacity_information_bound q hq0 hq1

private theorem capacity_joint_information_eq_iff (q : ℝ) (hq0 : 0 ≤ q)
    (hq1 : q ≤ 1) :
    oneUseJointMutualInformation q = Real.log (5 / 4) ↔ q = 2 / 5 := by
  rw [capacity_joint_information_eq_closed_form q hq0 hq1]
  exact capacity_information_eq_iff q hq0 hq1

private theorem capacity_block_is_distribution (n : ℕ) (input : Fin n → Route) :
    IsFiniteDistribution (blockChannel n input) := by
  constructor
  · intro output
    unfold blockChannel
    apply Finset.prod_nonneg
    intro i _
    exact (capacity_routeChannel_is_distribution (input i)).1 (output i)
  · unfold blockChannel
    calc
      (∑ output : Fin n → Bool, ∏ i, routeChannel (input i) (output i)) =
          ∏ i, ∑ output : Bool, routeChannel (input i) output :=
        (Fintype.prod_sum _).symm
      _ = ∏ _i : Fin n, (1 : ℝ) := by
        apply Finset.prod_congr rfl
        intro i _
        exact (capacity_routeChannel_is_distribution (input i)).2
      _ = 1 := by simp

private theorem capacity_block_zero (input : Fin 0 → Route) (output : Fin 0 → Bool) :
    blockChannel 0 input output = 1 := by
  simp [blockChannel]

private theorem capacity_block_one (input : Fin 1 → Route) (output : Fin 1 → Bool) :
    blockChannel 1 input output = routeChannel (input 0) (output 0) := by
  simp [blockChannel]

/-- The complete platform-shaped capacity result: the actual finite
joint-law mutual information equals its closed form on `[0, 1]` and has
capacity `log (5/4)` nats uniquely at routed-input probability `2/5`; the
memoryless product channel is normalized for every fixed input word. -/
theorem solution :
    (∀ q : ℝ, 0 ≤ q → q ≤ 1 →
      IsFiniteDistribution
        (fun x : Route × Bool => routedInputJointMass q x.1 x.2))
    ∧ (∀ prior : Route → ℝ, IsFiniteDistribution prior →
      ∃! q : ℝ, 0 ≤ q ∧ q ≤ 1 ∧ prior = routedInputPrior q)
    ∧ (∀ q : ℝ, 0 ≤ q → q ≤ 1 →
      oneUseJointMutualInformation q = oneUseMutualInformation q)
    ∧ (∀ q : ℝ, oneUseMutualInformation q =
      routedInputOutputEntropy q - routedInputConditionalEntropy q)
    ∧ (∀ q : ℝ, 0 ≤ q → q ≤ 1 →
      oneUseMutualInformation q ≤ Real.log (5 / 4)
        ∧ (oneUseMutualInformation q = Real.log (5 / 4) ↔ q = 2 / 5))
    ∧ (∀ q : ℝ, 0 ≤ q → q ≤ 1 →
      oneUseJointMutualInformation q ≤ Real.log (5 / 4)
        ∧ (oneUseJointMutualInformation q = Real.log (5 / 4) ↔ q = 2 / 5))
    ∧ oneUseMutualInformation (2 / 5) = Real.log (5 / 4)
    ∧ oneUseJointMutualInformation (2 / 5) = Real.log (5 / 4)
    ∧ ((∀ n : ℕ, ∀ input : Fin n → Route,
        IsFiniteDistribution (blockChannel n input))
      ∧ (∀ input : Fin 0 → Route, ∀ output : Fin 0 → Bool,
        blockChannel 0 input output = 1)
      ∧ ∀ input : Fin 1 → Route, ∀ output : Fin 1 → Bool,
        blockChannel 1 input output = routeChannel (input 0) (output 0)) := by
  refine ⟨?_, capacity_every_prior_is_parameterized, ?_,
    capacity_information_from_joint, ?_, ?_,
    capacity_information_at_two_fifths, capacity_joint_information_at_two_fifths,
    ⟨capacity_block_is_distribution, capacity_block_zero, capacity_block_one⟩⟩
  · intro q hq0 hq1
    exact capacity_joint_is_distribution hq0 hq1
  · intro q hq0 hq1
    exact capacity_joint_information_eq_closed_form q hq0 hq1
  · intro q hq0 hq1
    exact ⟨capacity_information_bound q hq0 hq1,
      capacity_information_eq_iff q hq0 hq1⟩
  · intro q hq0 hq1
    exact ⟨capacity_joint_information_bound q hq0 hq1,
      capacity_joint_information_eq_iff q hq0 hq1⟩

example : oneUseMutualInformation (2 / 5) = Real.log (5 / 4) :=
  capacity_information_at_two_fifths

example (n : ℕ) (input : Fin n → Route) :
    IsFiniteDistribution (blockChannel n input) :=
  capacity_block_is_distribution n input

#print axioms solution
