import Definitions.Def_TranscendenceTowerFiniteInformation

set_option autoImplicit false

open scoped BigOperators
open TranscendenceTower.FiniteInformation

private theorem fi_fstMarginal_nonneg {α β : Type} [Fintype α] [Fintype β]
    {joint : α → β → ℝ} (h : ∀ a b, 0 ≤ joint a b) (a : α) :
    0 ≤ fstMarginal joint a :=
  Finset.sum_nonneg fun b _ => h a b

private theorem fi_sndMarginal_nonneg {α β : Type} [Fintype α] [Fintype β]
    {joint : α → β → ℝ} (h : ∀ a b, 0 ≤ joint a b) (b : β) :
    0 ≤ sndMarginal joint b :=
  Finset.sum_nonneg fun a _ => h a b

private theorem fi_sum_sndMarginal {α β : Type} [Fintype α] [Fintype β]
    (joint : α → β → ℝ) :
    ∑ b, sndMarginal joint b = ∑ a, ∑ b, joint a b := by
  simp only [sndMarginal]
  exact Finset.sum_comm

private theorem fi_marginals_isDist {α β : Type} [Fintype α] [Fintype β]
    {joint : α → β → ℝ} (hnn : ∀ a b, 0 ≤ joint a b)
    (hsum : ∑ a, ∑ b, joint a b = 1) :
    IsDist (fstMarginal joint) ∧ IsDist (sndMarginal joint) :=
  ⟨⟨fi_fstMarginal_nonneg hnn, hsum⟩,
    ⟨fi_sndMarginal_nonneg hnn, by rw [fi_sum_sndMarginal]; exact hsum⟩⟩

private theorem fi_le_fstMarginal {α β : Type} [Fintype α] [Fintype β]
    {joint : α → β → ℝ} (hnn : ∀ a b, 0 ≤ joint a b) (a : α) (b : β) :
    joint a b ≤ fstMarginal joint a :=
  Finset.single_le_sum (f := fun b => joint a b)
    (fun b _ => hnn a b) (Finset.mem_univ b)

private theorem fi_le_sndMarginal {α β : Type} [Fintype α] [Fintype β]
    {joint : α → β → ℝ} (hnn : ∀ a b, 0 ≤ joint a b) (a : α) (b : β) :
    joint a b ≤ sndMarginal joint b :=
  Finset.single_le_sum (f := fun a => joint a b)
    (fun a _ => hnn a b) (Finset.mem_univ a)

private theorem fi_chain_rule_cell {j pa : ℝ} (hj : 0 ≤ j) (hle : j ≤ pa) :
    shannon j
      = (if j = 0 then 0 else j * Real.log (pa / j)) + j * Real.log pa⁻¹ := by
  by_cases hz : j = 0
  · simp [hz]
  · have hjpos : 0 < j := lt_of_le_of_ne hj (Ne.symm hz)
    have hpa : 0 < pa := lt_of_lt_of_le hjpos hle
    simp only [hz, if_false, shannon]
    rw [Real.log_div (ne_of_gt hpa) hz, Real.log_inv, Real.log_inv]
    ring

private theorem fi_chain_rule {α β : Type} [Fintype α] [Fintype β]
    {joint : α → β → ℝ} (hnn : ∀ a b, 0 ≤ joint a b) :
    jointEntropy joint = entropy (fstMarginal joint) + condEntropy joint := by
  unfold jointEntropy entropy condEntropy
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun a _ => ?_
  have hsplit : ∀ b ∈ (Finset.univ : Finset β),
      shannon (joint a b)
        = (if joint a b = 0 then 0
            else joint a b * Real.log (fstMarginal joint a / joint a b))
          + joint a b * Real.log (fstMarginal joint a)⁻¹ :=
    fun b _ => fi_chain_rule_cell (hnn a b) (fi_le_fstMarginal hnn a b)
  rw [Finset.sum_congr rfl hsplit, Finset.sum_add_distrib, ← Finset.sum_mul]
  simp only [shannon, fstMarginal]
  ring

private theorem fi_mutualInfo_cell {j pa pb : ℝ} (hj : 0 ≤ j) (hja : j ≤ pa)
    (hjb : j ≤ pb) :
    (if j = 0 then 0 else j * Real.log (j / (pa * pb)))
      = j * Real.log pa⁻¹ + j * Real.log pb⁻¹ - shannon j := by
  by_cases hz : j = 0
  · simp [hz]
  · have hjpos : 0 < j := lt_of_le_of_ne hj (Ne.symm hz)
    have hpa : 0 < pa := lt_of_lt_of_le hjpos hja
    have hpb : 0 < pb := lt_of_lt_of_le hjpos hjb
    simp only [hz, if_false, shannon]
    rw [Real.log_div hz (by positivity),
      Real.log_mul (ne_of_gt hpa) (ne_of_gt hpb),
      Real.log_inv, Real.log_inv, Real.log_inv]
    ring

private theorem fi_mutualInfo_eq_entropies {α β : Type} [Fintype α] [Fintype β]
    {joint : α → β → ℝ} (hnn : ∀ a b, 0 ≤ joint a b) :
    mutualInfo joint
      = entropy (fstMarginal joint) + entropy (sndMarginal joint)
        - jointEntropy joint := by
  have hrw : mutualInfo joint
      = ∑ a, ∑ b, (joint a b * Real.log (fstMarginal joint a)⁻¹
          + joint a b * Real.log (sndMarginal joint b)⁻¹
          - shannon (joint a b)) :=
    Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ =>
      fi_mutualInfo_cell (hnn a b) (fi_le_fstMarginal hnn a b)
        (fi_le_sndMarginal hnn a b)
  have e1 : ∑ a, ∑ b, joint a b * Real.log (fstMarginal joint a)⁻¹
      = entropy (fstMarginal joint) :=
    Finset.sum_congr rfl fun a _ => by rw [← Finset.sum_mul]; rfl
  have e2 : ∑ a, ∑ b, joint a b * Real.log (sndMarginal joint b)⁻¹
      = entropy (sndMarginal joint) := by
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun b _ => by rw [← Finset.sum_mul]; rfl
  rw [hrw]
  simp only [Finset.sum_sub_distrib, Finset.sum_add_distrib]
  rw [e1, e2]
  rfl

private theorem fi_sum_marginal_product {α β : Type} [Fintype α] [Fintype β]
    {joint : α → β → ℝ} (hnn : ∀ a b, 0 ≤ joint a b)
    (hsum : ∑ a, ∑ b, joint a b = 1) :
    ∑ a, ∑ b, fstMarginal joint a * sndMarginal joint b = 1 := by
  obtain ⟨⟨_, hfs⟩, ⟨_, hss⟩⟩ := fi_marginals_isDist hnn hsum
  have hrow : ∀ a ∈ (Finset.univ : Finset α),
      ∑ b, fstMarginal joint a * sndMarginal joint b
        = fstMarginal joint a * ∑ b, sndMarginal joint b :=
    fun a _ => (Finset.mul_sum _ _ _).symm
  rw [Finset.sum_congr rfl hrow, ← Finset.sum_mul, hfs, hss, one_mul]

private theorem fi_mutualInfo_nonneg {α β : Type} [Fintype α] [Fintype β]
    {joint : α → β → ℝ} (hnn : ∀ a b, 0 ≤ joint a b)
    (hsum : ∑ a, ∑ b, joint a b = 1) : 0 ≤ mutualInfo joint := by
  have hcell : ∀ a b,
      -(if joint a b = 0 then 0
        else joint a b *
          Real.log (joint a b / (fstMarginal joint a * sndMarginal joint b)))
        ≤ fstMarginal joint a * sndMarginal joint b - joint a b := by
    intro a b
    by_cases hz : joint a b = 0
    · rw [hz]
      simpa using mul_nonneg (fi_fstMarginal_nonneg hnn a) (fi_sndMarginal_nonneg hnn b)
    · have hjpos : 0 < joint a b := lt_of_le_of_ne (hnn a b) (Ne.symm hz)
      have hpa : 0 < fstMarginal joint a :=
        lt_of_lt_of_le hjpos (fi_le_fstMarginal hnn a b)
      have hpb : 0 < sndMarginal joint b :=
        lt_of_lt_of_le hjpos (fi_le_sndMarginal hnn a b)
      simp only [hz, if_false]
      have hflip : -(joint a b *
            Real.log (joint a b / (fstMarginal joint a * sndMarginal joint b)))
          = joint a b *
            Real.log ((fstMarginal joint a * sndMarginal joint b) / joint a b) := by
        rw [show (fstMarginal joint a * sndMarginal joint b) / joint a b
              = (joint a b / (fstMarginal joint a * sndMarginal joint b))⁻¹ from
            (inv_div _ _).symm, Real.log_inv]
        ring
      rw [hflip]
      have hlog :
          Real.log ((fstMarginal joint a * sndMarginal joint b) / joint a b)
            ≤ (fstMarginal joint a * sndMarginal joint b) / joint a b - 1 :=
        Real.log_le_sub_one_of_pos (by positivity)
      calc joint a b *
              Real.log ((fstMarginal joint a * sndMarginal joint b) / joint a b)
          ≤ joint a b *
              ((fstMarginal joint a * sndMarginal joint b) / joint a b - 1) :=
            mul_le_mul_of_nonneg_left hlog (le_of_lt hjpos)
        _ = fstMarginal joint a * sndMarginal joint b - joint a b := by field_simp
  have hle : -mutualInfo joint
      ≤ ∑ a, ∑ b, (fstMarginal joint a * sndMarginal joint b - joint a b) := by
    unfold mutualInfo
    rw [← Finset.sum_neg_distrib]
    refine Finset.sum_le_sum fun a _ => ?_
    rw [← Finset.sum_neg_distrib]
    exact Finset.sum_le_sum fun b _ => hcell a b
  have hzero : ∑ a, ∑ b, (fstMarginal joint a * sndMarginal joint b - joint a b)
      = 0 := by
    simp only [Finset.sum_sub_distrib]
    rw [fi_sum_marginal_product hnn hsum, hsum, sub_self]
  linarith [hle, hzero.ge, hzero.le]

private theorem fi_condEntropy_nonneg {α β : Type} [Fintype α] [Fintype β]
    {joint : α → β → ℝ} (hnn : ∀ a b, 0 ≤ joint a b) :
    0 ≤ condEntropy joint := by
  unfold condEntropy
  refine Finset.sum_nonneg fun a _ => Finset.sum_nonneg fun b _ => ?_
  by_cases hz : joint a b = 0
  · simp [hz]
  · have hjpos : 0 < joint a b := lt_of_le_of_ne (hnn a b) (Ne.symm hz)
    simp only [hz, if_false]
    exact mul_nonneg (le_of_lt hjpos)
      (Real.log_nonneg ((one_le_div hjpos).mpr (fi_le_fstMarginal hnn a b)))

/-- Discrete Shannon information theory over arbitrary finite alphabets. -/
theorem solution (α β : Type) [Fintype α] [Fintype β] :
    (∀ joint : α → β → ℝ, (∀ a b, 0 ≤ joint a b) →
        (∑ a, ∑ b, joint a b = 1) →
        IsDist (fstMarginal joint) ∧ IsDist (sndMarginal joint))
    ∧ (∀ joint : α → β → ℝ, (∀ a b, 0 ≤ joint a b) →
        jointEntropy joint = entropy (fstMarginal joint) + condEntropy joint)
    ∧ (∀ joint : α → β → ℝ, (∀ a b, 0 ≤ joint a b) →
        mutualInfo joint = entropy (fstMarginal joint)
          + entropy (sndMarginal joint) - jointEntropy joint)
    ∧ (∀ joint : α → β → ℝ, (∀ a b, 0 ≤ joint a b) →
        (∑ a, ∑ b, joint a b = 1) → 0 ≤ mutualInfo joint)
    ∧ (∀ joint : α → β → ℝ, (∀ a b, 0 ≤ joint a b) →
        (∑ a, ∑ b, joint a b = 1) →
        jointEntropy joint
          ≤ entropy (fstMarginal joint) + entropy (sndMarginal joint))
    ∧ (∀ joint : α → β → ℝ, (∀ a b, 0 ≤ joint a b) → 0 ≤ condEntropy joint)
    ∧ (∀ joint : α → β → ℝ, (∀ a b, 0 ≤ joint a b) →
        mutualInfo joint = entropy (sndMarginal joint) - condEntropy joint)
    ∧ (∀ joint : α → β → ℝ, (∀ a b, 0 ≤ joint a b) →
        mutualInfo joint ≤ entropy (sndMarginal joint)) := by
  refine ⟨fun _ hnn hsum => fi_marginals_isDist hnn hsum,
    fun _ hnn => fi_chain_rule hnn,
    fun _ hnn => fi_mutualInfo_eq_entropies hnn,
    fun _ hnn hsum => fi_mutualInfo_nonneg hnn hsum, ?_,
    fun _ hnn => fi_condEntropy_nonneg hnn, ?_, ?_⟩
  · intro joint hnn hsum
    have h := fi_mutualInfo_nonneg hnn hsum
    rw [fi_mutualInfo_eq_entropies hnn] at h
    linarith
  · intro joint hnn
    rw [fi_mutualInfo_eq_entropies hnn, fi_chain_rule hnn]
    ring
  · intro joint hnn
    have hcond := fi_condEntropy_nonneg hnn
    have heq : mutualInfo joint
        = entropy (sndMarginal joint) - condEntropy joint := by
      rw [fi_mutualInfo_eq_entropies hnn, fi_chain_rule hnn]; ring
    linarith

#print axioms solution
