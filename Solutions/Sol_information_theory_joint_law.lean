import Definitions.Def_InformationTheory

set_option autoImplicit false

open scoped BigOperators
open TranscendenceTower TranscendenceTower.ContextTheories
  TranscendenceTower.Lifting
open TranscendenceTower.InformationTheoryPlatform

private theorem it_admissible_direct : Admissible srcP tgtNand ∅ := by
  refine ⟨vP, ?_⟩
  rintro x (rfl | ⟨rfl, _⟩)
  · rfl
  · rfl

private theorem it_direct_minblock (A : Set L0) :
    MinBlock srcP tgtNand A ↔ A = ∅ := by
  constructor
  · intro hA
    apply Set.Subset.antisymm
    · exact hA.2 ∅ it_admissible_direct (Set.empty_subset A)
    · exact Set.empty_subset A
  · rintro rfl
    exact ⟨it_admissible_direct, fun B _ _ => Set.empty_subset B⟩

private theorem it_not_admissible_empty : ¬ Admissible srcPQ tgtNand ∅ := by
  rintro ⟨v, hv⟩
  have hp : Form.eval v pA = true := hv pA (Or.inr ⟨Or.inl rfl, fun h => h⟩)
  have hq : Form.eval v qA = true := hv qA (Or.inr ⟨Or.inr rfl, fun h => h⟩)
  have hn : Form.eval v (Form.neg (Form.conj pA qA)) = true := hv _ (Or.inl rfl)
  rw [show Form.eval v (Form.neg (Form.conj pA qA)) =
        !((Form.eval v pA) && (Form.eval v qA)) from rfl, hp, hq] at hn
  exact absurd hn (by decide)

private theorem it_admissible_drop_p : Admissible srcPQ tgtNand {pA} := by
  refine ⟨vQ, ?_⟩
  rintro x (rfl | ⟨hx, hxA⟩)
  · rfl
  · rcases hx with rfl | rfl
    · exact absurd rfl hxA
    · rfl

private theorem it_admissible_drop_q : Admissible srcPQ tgtNand {qA} := by
  refine ⟨vP, ?_⟩
  rintro x (rfl | ⟨hx, hxA⟩)
  · rfl
  · rcases hx with rfl | rfl
    · rfl
    · exact absurd rfl hxA

private theorem it_minblock_singleton {r : L0}
    (hadm : Admissible srcPQ tgtNand {r}) : MinBlock srcPQ tgtNand {r} := by
  refine ⟨hadm, fun B hB hsub => ?_⟩
  by_cases hr : r ∈ B
  · intro x hx
    rcases hx with rfl
    exact hr
  · exfalso
    have hBempty : B = ∅ := by
      ext y
      constructor
      · intro hy
        have hyr : y = r := hsub hy
        subst hyr
        exact absurd hy hr
      · intro hy
        exact hy.elim
    rw [hBempty] at hB
    exact it_not_admissible_empty hB

private theorem it_admissible_contains_p_or_q {A : Set L0}
    (hA : Admissible srcPQ tgtNand A) : pA ∈ A ∨ qA ∈ A := by
  rcases hA with ⟨v, hv⟩
  by_contra h
  push Not at h
  have hp : Form.eval v pA = true := hv pA (Or.inr ⟨Or.inl rfl, h.1⟩)
  have hq : Form.eval v qA = true := hv qA (Or.inr ⟨Or.inr rfl, h.2⟩)
  have hn : Form.eval v (Form.neg (Form.conj pA qA)) = true := hv _ (Or.inl rfl)
  rw [show Form.eval v (Form.neg (Form.conj pA qA)) =
        !((Form.eval v pA) && (Form.eval v qA)) from rfl, hp, hq] at hn
  exact absurd hn (by decide)

private theorem it_routed_minblock_iff (A : Set L0) :
    MinBlock srcPQ tgtNand A ↔ A = {pA} ∨ A = {qA} := by
  constructor
  · intro hA
    rcases it_admissible_contains_p_or_q hA.1 with hp | hq
    · left
      have hsmall : ({pA} : Set L0) ⊆ A := by
        intro x hx
        rw [Set.mem_singleton_iff.mp hx]
        exact hp
      exact Set.Subset.antisymm
        (hA.2 {pA} it_admissible_drop_p hsmall) hsmall
    · right
      have hsmall : ({qA} : Set L0) ⊆ A := by
        intro x hx
        rw [Set.mem_singleton_iff.mp hx]
        exact hq
      exact Set.Subset.antisymm
        (hA.2 {qA} it_admissible_drop_q hsmall) hsmall
  · rintro (rfl | rfl)
    · exact it_minblock_singleton it_admissible_drop_p
    · exact it_minblock_singleton it_admissible_drop_q

private theorem it_routed_labels_exactly_actual_blocks (A : Set L0) :
    MinBlock srcPQ tgtNand A ↔ ∃ r : RoutedResolution, A = routedBlock r := by
  rw [it_routed_minblock_iff]
  constructor
  · rintro (rfl | rfl)
    · exact ⟨.dropP, rfl⟩
    · exact ⟨.dropQ, rfl⟩
  · rintro ⟨r, rfl⟩
    cases r <;> simp [routedBlock]

private theorem it_direct_mass_is_distribution :
    IsFiniteDistribution directSingletonMass := by
  constructor
  · intro r
    simp [directSingletonMass]
  · rw [sum_unit]
    norm_num [directSingletonMass]

private theorem it_routed_mass_is_distribution :
    IsFiniteDistribution uniformRoutedSelectionMass := by
  constructor
  · intro r
    norm_num [uniformRoutedSelectionMass]
  · rw [sum_resolutions]
    norm_num [uniformRoutedSelectionMass]

private theorem it_routed_mass_symmetric :
    ∀ r, uniformRoutedSelectionMass r = uniformRoutedSelectionMass (swapResolution r) := by
  intro r
  cases r <;> norm_num [uniformRoutedSelectionMass, swapResolution]

private theorem it_direct_entropy : finiteEntropy directSingletonMass = 0 := by
  unfold finiteEntropy
  rw [sum_unit]
  norm_num [shannonTerm, directSingletonMass]

private theorem it_routed_entropy : finiteEntropy uniformRoutedSelectionMass = Real.log 2 := by
  unfold finiteEntropy
  rw [sum_resolutions]
  norm_num [shannonTerm, uniformRoutedSelectionMass]
  ring

private theorem it_joint_nonnegative (r : Route) (output : Bool) : 0 ≤ jointMass r output := by
  cases r <;> cases output <;>
    norm_num [jointMass, uniformRoutePrior, routeChannel]

private theorem it_joint_normalized :
    ∑ r : Route, ∑ output : Bool, jointMass r output = 1 := by
  rw [sum_routes]
  simp_rw [sum_bools]
  norm_num [jointMass, uniformRoutePrior, routeChannel]

private theorem it_output_failure : outputMarginal false = 1 / 4 := by
  rw [outputMarginal, sum_routes]
  norm_num [jointMass, uniformRoutePrior, routeChannel]

private theorem it_output_survival : outputMarginal true = 3 / 4 := by
  rw [outputMarginal, sum_routes]
  norm_num [jointMass, uniformRoutePrior, routeChannel]

private theorem it_conditional_entropy :
    uniformRouteConditionalEntropy = Real.log 2 / 2 := by
  unfold uniformRouteConditionalEntropy finiteEntropy routeConditionalMass
  simp_rw [sum_routes, sum_bools]
  norm_num [routeMarginal, jointMass, uniformRoutePrior, routeChannel, shannonTerm]
  ring

private theorem it_log_four_eq_two_log_two : Real.log 4 = 2 * Real.log 2 := by
  have h := Real.log_mul (show (2 : ℝ) ≠ 0 by norm_num)
    (show (2 : ℝ) ≠ 0 by norm_num)
  norm_num at h ⊢
  linarith

private theorem it_log_two_thirds :
    Real.log (2 / 3 : ℝ) = Real.log (4 / 3 : ℝ) - Real.log 2 := by
  rw [Real.log_div (by norm_num) (by norm_num),
    Real.log_div (by norm_num) (by norm_num), it_log_four_eq_two_log_two]
  ring

private theorem it_output_entropy :
    uniformRouteOutputEntropy = Real.binEntropy (3 / 4) := by
  unfold uniformRouteOutputEntropy finiteEntropy
  rw [sum_bools, it_output_failure, it_output_survival]
  norm_num [shannonTerm, Real.binEntropy]
  ring

private theorem it_mutual_information_from_joint :
    uniformRouteMutualInformation =
      uniformRouteOutputEntropy - uniformRouteConditionalEntropy := by
  unfold uniformRouteMutualInformation finiteMutualInformation
    uniformRouteOutputEntropy uniformRouteConditionalEntropy finiteEntropy
    routeConditionalMass routeMarginal outputMarginal jointMass uniformRoutePrior
    routeChannel shannonTerm
  simp_rw [sum_routes, sum_bools]
  norm_num
  rw [it_log_two_thirds, it_log_four_eq_two_log_two]
  ring

private theorem it_mutual_information : uniformRouteMutualInformation =
    Real.binEntropy (3 / 4) - Real.log 2 / 2 := by
  rw [it_mutual_information_from_joint, it_output_entropy, it_conditional_entropy]

private theorem it_loss_row_is_distribution (s : ℝ) (hs0 : 0 ≤ s) (hs1 : s ≤ 1)
    (input : Bool) : IsFiniteDistribution (lossChannel s input) := by
  constructor
  · intro output
    cases input <;> cases output <;> simp [lossChannel] <;> linarith
  · cases input <;> simp [lossChannel]

private theorem it_loss_compose_algebraic (s t : ℝ) (input output : Bool) :
    composeLossChannel s t input output = lossChannel (s * t) input output := by
  cases input <;> cases output <;>
    (simp [composeLossChannel, lossChannel] <;> ring)

private theorem it_fresh_stage_composition (s t : ℝ)
    (hs0 : 0 ≤ s) (hs1 : s ≤ 1) (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    composeLossChannel s t = lossChannel (s * t)
      ∧ ∀ input, IsFiniteDistribution (composeLossChannel s t input) := by
  constructor
  · funext input output
    exact it_loss_compose_algebraic s t input output
  · intro input
    have hcompose : composeLossChannel s t input = lossChannel (s * t) input := by
      funext output
      exact it_loss_compose_algebraic s t input output
    rw [hcompose]
    apply it_loss_row_is_distribution
    · exact mul_nonneg hs0 ht0
    · calc
        s * t ≤ 1 * t := mul_le_mul_of_nonneg_right hs1 ht0
        _ ≤ 1 * 1 := mul_le_mul_of_nonneg_left ht1 (by norm_num)
        _ = 1 := by norm_num

/-- The complete platform-shaped finite information-theory result. -/
theorem solution :
    ((∀ A : Set L0, MinBlock srcPQ tgtNand A ↔ A = {pA} ∨ A = {qA})
      ∧ (∀ A : Set L0, MinBlock srcPQ tgtNand A ↔
        ∃ r : RoutedResolution, A = routedBlock r))
    ∧ ((∀ A : Set L0, MinBlock srcP tgtNand A ↔ A = ∅)
      ∧ IsFiniteDistribution directSingletonMass
      ∧ finiteEntropy directSingletonMass = 0)
    ∧ (IsFiniteDistribution uniformRoutedSelectionMass
      ∧ (∀ r, uniformRoutedSelectionMass r =
        uniformRoutedSelectionMass (swapResolution r))
      ∧ finiteEntropy uniformRoutedSelectionMass = Real.log 2)
    ∧ ((∀ r output, 0 ≤ jointMass r output)
      ∧ (∑ r : Route, ∑ output : Bool, jointMass r output = 1)
      ∧ outputMarginal true = 3 / 4
      ∧ uniformRouteConditionalEntropy = Real.log 2 / 2
      ∧ uniformRouteMutualInformation = Real.binEntropy (3 / 4) - Real.log 2 / 2)
    ∧ ((∀ s t : ℝ, 0 ≤ s → s ≤ 1 → 0 ≤ t → t ≤ 1 →
        composeLossChannel s t = lossChannel (s * t)
          ∧ ∀ input, IsFiniteDistribution (composeLossChannel s t input))
      ∧ composeLossChannel (1 / 2) (1 / 2) true true = 1 / 4) := by
  refine ⟨⟨?_, ?_⟩, ⟨?_, ?_, ?_⟩, ⟨?_, ?_, ?_⟩, ⟨?_, ?_, ?_, ?_, ?_⟩, ⟨?_, ?_⟩⟩
  · exact it_routed_minblock_iff
  · exact it_routed_labels_exactly_actual_blocks
  · exact it_direct_minblock
  · exact it_direct_mass_is_distribution
  · exact it_direct_entropy
  · exact it_routed_mass_is_distribution
  · exact it_routed_mass_symmetric
  · exact it_routed_entropy
  · exact it_joint_nonnegative
  · exact it_joint_normalized
  · exact it_output_survival
  · exact it_conditional_entropy
  · exact it_mutual_information
  · intro s t hs0 hs1 ht0 ht1
    exact it_fresh_stage_composition s t hs0 hs1 ht0 ht1
  · have h := it_loss_compose_algebraic (1 / 2) (1 / 2) true true
    rw [h]
    norm_num [lossChannel]
