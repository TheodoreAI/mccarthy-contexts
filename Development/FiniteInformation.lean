/-
  Generic finite Shannon information theory.

  Mathlib supplies `Real.binEntropy` and a measure-theoretic Kullback-Leibler
  divergence, but no discrete entropy, conditional entropy or mutual
  information over finite alphabets.  This module builds them over arbitrary
  `Fintype`s, so that statements about product alphabets such as
  `Fin n → Route` are expressible at all.

  The companion route/survival development fixes the alphabets to `Route` and
  `Bool`; nothing in this file mentions them.  Everything is a finite sum, in
  nats, with zero-mass cells contributing zero by convention.
-/

import Mathlib.Analysis.SpecialFunctions.BinaryEntropy
import Mathlib.Analysis.MeanInequalities

set_option autoImplicit false

open scoped BigOperators
open Finset

namespace TranscendenceTower.FiniteInformation

noncomputable section

variable {α β : Type} [Fintype α] [Fintype β]

/-! ## Masses -/

/-- A finite mass function is a distribution when it is nonnegative and sums
to one. -/
def IsDist (mass : α → ℝ) : Prop :=
  (∀ x, 0 ≤ mass x) ∧ ∑ x, mass x = 1

/-- The Shannon summand, in nats, with the standard `0 log 0 = 0`
convention supplied by `Real.log 0 = 0`. -/
def shannon (p : ℝ) : ℝ := p * Real.log p⁻¹

@[simp] theorem shannon_zero : shannon (0 : ℝ) = 0 := by simp [shannon]

@[simp] theorem shannon_one : shannon (1 : ℝ) = 0 := by simp [shannon]

/-- Shannon entropy of a finite mass function, in nats. -/
def entropy (mass : α → ℝ) : ℝ := ∑ x, shannon (mass x)

/-! ## Joint laws, marginals and conditionals -/

/-- The first marginal of a joint law. -/
def fstMarginal (joint : α → β → ℝ) : α → ℝ := fun a => ∑ b, joint a b

/-- The second marginal of a joint law. -/
def sndMarginal (joint : α → β → ℝ) : β → ℝ := fun b => ∑ a, joint a b

/-- Joint entropy of a law on `α × β`. -/
def jointEntropy (joint : α → β → ℝ) : ℝ :=
  ∑ a, ∑ b, shannon (joint a b)

/-- The information-theoretic conditional entropy `H(β ∣ α)`, defined
directly as the joint sum `∑ p(a,b) log (p(a) / p(a,b))`.  Cells of zero
mass contribute zero. -/
def condEntropy (joint : α → β → ℝ) : ℝ :=
  ∑ a, ∑ b,
    if joint a b = 0 then 0
    else joint a b * Real.log (fstMarginal joint a / joint a b)

/-- Mutual information of a joint law against its own marginals, in nats.
Cells of zero mass contribute zero. -/
def mutualInfo (joint : α → β → ℝ) : ℝ :=
  ∑ a, ∑ b,
    if joint a b = 0 then 0
    else joint a b *
      Real.log (joint a b / (fstMarginal joint a * sndMarginal joint b))

/-! ## Marginals of a distribution are distributions -/

theorem fstMarginal_nonneg {joint : α → β → ℝ} (h : ∀ a b, 0 ≤ joint a b)
    (a : α) : 0 ≤ fstMarginal joint a :=
  Finset.sum_nonneg fun b _ => h a b

theorem sndMarginal_nonneg {joint : α → β → ℝ} (h : ∀ a b, 0 ≤ joint a b)
    (b : β) : 0 ≤ sndMarginal joint b :=
  Finset.sum_nonneg fun a _ => h a b

theorem sum_fstMarginal (joint : α → β → ℝ) :
    ∑ a, fstMarginal joint a = ∑ a, ∑ b, joint a b := rfl

theorem sum_sndMarginal (joint : α → β → ℝ) :
    ∑ b, sndMarginal joint b = ∑ a, ∑ b, joint a b := by
  simp only [sndMarginal]
  exact Finset.sum_comm

/-- Both marginals of a joint distribution are distributions. -/
theorem marginals_isDist {joint : α → β → ℝ}
    (hnn : ∀ a b, 0 ≤ joint a b) (hsum : ∑ a, ∑ b, joint a b = 1) :
    IsDist (fstMarginal joint) ∧ IsDist (sndMarginal joint) :=
  ⟨⟨fstMarginal_nonneg hnn, by rw [sum_fstMarginal]; exact hsum⟩,
    ⟨sndMarginal_nonneg hnn, by rw [sum_sndMarginal]; exact hsum⟩⟩

/-! ## The chain rule

`H(α, β) = H(α) + H(β ∣ α)`, proved cellwise.  The zero-mass guard in
`condEntropy` is exactly what makes the cellwise identity hold without a
positivity hypothesis on the marginals. -/

/-- The cellwise form of the chain rule. -/
theorem chain_rule_cell {j pa : ℝ} (hj : 0 ≤ j) (hle : j ≤ pa) :
    shannon j = (if j = 0 then 0 else j * Real.log (pa / j)) + j * Real.log pa⁻¹ := by
  by_cases hz : j = 0
  · simp [hz]
  · have hjpos : 0 < j := lt_of_le_of_ne hj (Ne.symm hz)
    have hpa : 0 < pa := lt_of_lt_of_le hjpos hle
    simp only [hz, if_false, shannon]
    rw [Real.log_div (ne_of_gt hpa) hz, Real.log_inv, Real.log_inv]
    ring

/-- **Chain rule.** For a joint law whose cells are nonnegative, the joint
entropy splits as the entropy of the first marginal plus the conditional
entropy of the second given the first. -/
theorem chain_rule {joint : α → β → ℝ} (hnn : ∀ a b, 0 ≤ joint a b) :
    jointEntropy joint = entropy (fstMarginal joint) + condEntropy joint := by
  unfold jointEntropy entropy condEntropy
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun a _ => ?_
  have hcell : ∀ b ∈ (Finset.univ : Finset β), joint a b ≤ fstMarginal joint a :=
    fun b hb => Finset.single_le_sum (f := fun b => joint a b)
      (fun b _ => hnn a b) hb
  have hsplit : ∀ b ∈ (Finset.univ : Finset β),
      shannon (joint a b)
        = (if joint a b = 0 then 0
            else joint a b * Real.log (fstMarginal joint a / joint a b))
          + joint a b * Real.log (fstMarginal joint a)⁻¹ :=
    fun b hb => chain_rule_cell (hnn a b) (hcell b hb)
  rw [Finset.sum_congr rfl hsplit, Finset.sum_add_distrib, ← Finset.sum_mul]
  simp only [shannon, fstMarginal]
  ring

/-! ## Mutual information as a difference of entropies -/

/-- The cellwise form of `I = H(α) + H(β) - H(α, β)`. -/
theorem mutualInfo_cell {j pa pb : ℝ} (hj : 0 ≤ j) (hja : j ≤ pa) (hjb : j ≤ pb) :
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

/-- **Mutual information as a difference of entropies.**
`I(α;β) = H(α) + H(β) - H(α, β)`, for any nonnegative joint law. -/
theorem mutualInfo_eq_entropies {joint : α → β → ℝ} (hnn : ∀ a b, 0 ≤ joint a b) :
    mutualInfo joint
      = entropy (fstMarginal joint) + entropy (sndMarginal joint)
        - jointEntropy joint := by
  have hja : ∀ a b, joint a b ≤ fstMarginal joint a := fun a b =>
    Finset.single_le_sum (f := fun b => joint a b)
      (fun b _ => hnn a b) (Finset.mem_univ b)
  have hjb : ∀ a b, joint a b ≤ sndMarginal joint b := fun a b =>
    Finset.single_le_sum (f := fun a => joint a b)
      (fun a _ => hnn a b) (Finset.mem_univ a)
  have hrw : mutualInfo joint
      = ∑ a, ∑ b, (joint a b * Real.log (fstMarginal joint a)⁻¹
          + joint a b * Real.log (sndMarginal joint b)⁻¹
          - shannon (joint a b)) :=
    Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ =>
      mutualInfo_cell (hnn a b) (hja a b) (hjb a b)
  have e1 : ∑ a, ∑ b, joint a b * Real.log (fstMarginal joint a)⁻¹
      = entropy (fstMarginal joint) :=
    Finset.sum_congr rfl fun a _ => by
      rw [← Finset.sum_mul]; rfl
  have e2 : ∑ a, ∑ b, joint a b * Real.log (sndMarginal joint b)⁻¹
      = entropy (sndMarginal joint) := by
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun b _ => by rw [← Finset.sum_mul]; rfl
  rw [hrw]
  simp only [Finset.sum_sub_distrib, Finset.sum_add_distrib]
  rw [e1, e2]
  rfl

/-! ## Nonnegativity, and subadditivity of entropy

Gibbs' inequality, in the form `I(α;β) ≥ 0`.  The proof is the standard
`log x ≤ x - 1` bound applied cellwise; the zero-mass cells are discharged
separately, where the bound degenerates to `0 ≤ p(a)p(b)`. -/

/-- The product of the two marginals is itself a distribution on `α × β`. -/
theorem sum_marginal_product {joint : α → β → ℝ}
    (hnn : ∀ a b, 0 ≤ joint a b) (hsum : ∑ a, ∑ b, joint a b = 1) :
    ∑ a, ∑ b, fstMarginal joint a * sndMarginal joint b = 1 := by
  obtain ⟨⟨_, hfs⟩, ⟨_, hss⟩⟩ := marginals_isDist hnn hsum
  have hrow : ∀ a ∈ (Finset.univ : Finset α),
      ∑ b, fstMarginal joint a * sndMarginal joint b
        = fstMarginal joint a * ∑ b, sndMarginal joint b :=
    fun a _ => (Finset.mul_sum _ _ _).symm
  rw [Finset.sum_congr rfl hrow, ← Finset.sum_mul, hfs, hss, one_mul]

/-- **Gibbs' inequality / nonnegativity of mutual information.**
A joint law is never less informative than the product of its marginals. -/
theorem mutualInfo_nonneg {joint : α → β → ℝ} (hnn : ∀ a b, 0 ≤ joint a b)
    (hsum : ∑ a, ∑ b, joint a b = 1) : 0 ≤ mutualInfo joint := by
  obtain ⟨⟨hfa, _⟩, ⟨hsa, _⟩⟩ := marginals_isDist hnn hsum
  have hja : ∀ a b, joint a b ≤ fstMarginal joint a := fun a b =>
    Finset.single_le_sum (f := fun b => joint a b)
      (fun b _ => hnn a b) (Finset.mem_univ b)
  have hjb : ∀ a b, joint a b ≤ sndMarginal joint b := fun a b =>
    Finset.single_le_sum (f := fun a => joint a b)
      (fun a _ => hnn a b) (Finset.mem_univ a)
  -- Cellwise: the negated summand is bounded by `p(a)p(b) - p(a,b)`.
  have hcell : ∀ a b,
      -(if joint a b = 0 then 0
        else joint a b *
          Real.log (joint a b / (fstMarginal joint a * sndMarginal joint b)))
        ≤ fstMarginal joint a * sndMarginal joint b - joint a b := by
    intro a b
    by_cases hz : joint a b = 0
    · rw [hz]
      simpa using mul_nonneg (hfa a) (hsa b)
    · have hjpos : 0 < joint a b := lt_of_le_of_ne (hnn a b) (Ne.symm hz)
      have hpa : 0 < fstMarginal joint a := lt_of_lt_of_le hjpos (hja a b)
      have hpb : 0 < sndMarginal joint b := lt_of_lt_of_le hjpos (hjb a b)
      have hP : 0 < fstMarginal joint a * sndMarginal joint b := mul_pos hpa hpb
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
        _ = fstMarginal joint a * sndMarginal joint b - joint a b := by
            field_simp
  -- Summing the cellwise bound gives `-I ≤ 1 - 1 = 0`.
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
    rw [sum_marginal_product hnn hsum, hsum, sub_self]
  linarith [hle, hzero.ge, hzero.le]

/-- **Subadditivity of entropy**, an immediate corollary:
`H(α, β) ≤ H(α) + H(β)`. -/
theorem jointEntropy_le_add {joint : α → β → ℝ} (hnn : ∀ a b, 0 ≤ joint a b)
    (hsum : ∑ a, ∑ b, joint a b = 1) :
    jointEntropy joint ≤ entropy (fstMarginal joint) + entropy (sndMarginal joint) := by
  have h := mutualInfo_nonneg hnn hsum
  rw [mutualInfo_eq_entropies hnn] at h
  linarith

/-! ## Toward the converse

`I = H(β) - H(β ∣ α)` together with `H(β ∣ α) ≥ 0` bounds the information a
single channel use can carry by the entropy of its output.  This is the
single-letter ingredient of the weak converse; the `n`-letter step
(`I(αⁿ;βⁿ) ≤ n·C`) additionally needs conditional mutual information and is
not developed here. -/

/-- **Conditional entropy is nonnegative.**  Each cell compares a joint mass
against the larger marginal that dominates it. -/
theorem condEntropy_nonneg {joint : α → β → ℝ} (hnn : ∀ a b, 0 ≤ joint a b) :
    0 ≤ condEntropy joint := by
  unfold condEntropy
  refine Finset.sum_nonneg fun a _ => Finset.sum_nonneg fun b _ => ?_
  by_cases hz : joint a b = 0
  · simp [hz]
  · have hjpos : 0 < joint a b := lt_of_le_of_ne (hnn a b) (Ne.symm hz)
    have hja : joint a b ≤ fstMarginal joint a :=
      Finset.single_le_sum (f := fun b => joint a b)
        (fun b _ => hnn a b) (Finset.mem_univ b)
    simp only [hz, if_false]
    exact mul_nonneg (le_of_lt hjpos)
      (Real.log_nonneg ((one_le_div hjpos).mpr hja))

/-- **The standard form of mutual information**, `I(α;β) = H(β) - H(β ∣ α)`. -/
theorem mutualInfo_eq_sub_condEntropy {joint : α → β → ℝ}
    (hnn : ∀ a b, 0 ≤ joint a b) :
    mutualInfo joint = entropy (sndMarginal joint) - condEntropy joint := by
  rw [mutualInfo_eq_entropies hnn, chain_rule hnn]
  ring

/-- **One channel use carries at most the output entropy.**
`I(α;β) ≤ H(β)`. -/
theorem mutualInfo_le_entropy_snd {joint : α → β → ℝ}
    (hnn : ∀ a b, 0 ≤ joint a b) :
    mutualInfo joint ≤ entropy (sndMarginal joint) := by
  rw [mutualInfo_eq_sub_condEntropy hnn]
  linarith [condEntropy_nonneg hnn]

section Verification

#print axioms marginals_isDist
#print axioms chain_rule
#print axioms mutualInfo_eq_entropies
#print axioms mutualInfo_nonneg
#print axioms jointEntropy_le_add
#print axioms condEntropy_nonneg
#print axioms mutualInfo_eq_sub_condEntropy
#print axioms mutualInfo_le_entropy_snd

end Verification

end

end TranscendenceTower.FiniteInformation
