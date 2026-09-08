/-
  Fano's inequality over finite alphabets.

  If a guess is usually right, then little uncertainty about the truth
  remains once the guess is known.  For a joint law on (guess, truth) with
  error probability `Pe`,

    H(truth | guess) ≤ h(Pe) + Pe * log M,

  where `h` is the binary entropy `shannon Pe + shannon (1 - Pe)` and `M` is
  the alphabet size.

  The textbook bound carries `log (M - 1)`.  We prove the slightly weaker
  `log M`, which is what a weak converse needs, because it lets the
  comparison law be a *sub*-probability and so removes all counting of the
  off-diagonal.  The proof is Gibbs' inequality against that comparison law:
  put the correct-answer mass on the guess, and spread `Pe / M` over every
  answer.  Its rows sum to at most one, which is all the argument uses.
-/

import Development.FiniteInformation

set_option autoImplicit false

open scoped BigOperators

namespace TranscendenceTower.FiniteInformation

noncomputable section

variable {γ : Type} [Fintype γ] [DecidableEq γ]

/-! ## Correct and erroneous mass -/

/-- Probability that the guess equals the truth. -/
def correctProb (J : γ → γ → ℝ) : ℝ := ∑ g, J g g

/-- Probability that the guess differs from the truth. -/
def errorProb (J : γ → γ → ℝ) : ℝ := ∑ g, ∑ w, if w = g then 0 else J g w

theorem correct_add_error (J : γ → γ → ℝ) :
    correctProb J + errorProb J = ∑ g, ∑ w, J g w := by
  unfold correctProb errorProb
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun g _ => ?_
  symm
  have hsplit : ∀ w ∈ (Finset.univ : Finset γ),
      J g w = (if w = g then J g w else 0) + (if w = g then 0 else J g w) :=
    fun w _ => by by_cases h : w = g <;> simp [h]
  rw [Finset.sum_congr rfl hsplit, Finset.sum_add_distrib,
    Finset.sum_ite_eq' Finset.univ g (fun w => J g w)]
  simp

theorem correctProb_nonneg {J : γ → γ → ℝ} (hnn : ∀ g w, 0 ≤ J g w) :
    0 ≤ correctProb J :=
  Finset.sum_nonneg fun g _ => hnn g g

theorem errorProb_nonneg {J : γ → γ → ℝ} (hnn : ∀ g w, 0 ≤ J g w) :
    0 ≤ errorProb J :=
  Finset.sum_nonneg fun g _ => Finset.sum_nonneg fun w _ => by
    by_cases h : w = g <;> simp [h, hnn]

theorem le_correctProb {J : γ → γ → ℝ} (hnn : ∀ g w, 0 ≤ J g w) (g : γ) :
    J g g ≤ correctProb J :=
  Finset.single_le_sum (f := fun g => J g g) (fun g _ => hnn g g)
    (Finset.mem_univ g)

theorem le_errorProb {J : γ → γ → ℝ} (hnn : ∀ g w, 0 ≤ J g w) {g w : γ}
    (hwg : w ≠ g) : J g w ≤ errorProb J := by
  have hrownn : ∀ g' : γ, 0 ≤ ∑ w', if w' = g' then 0 else J g' w' :=
    fun g' => Finset.sum_nonneg fun w' _ => by
      by_cases h : w' = g' <;> simp [h, hnn]
  have h1 : (if w = g then 0 else J g w)
      ≤ ∑ w', if w' = g then 0 else J g w' :=
    Finset.single_le_sum (f := fun w' => if w' = g then 0 else J g w')
      (fun w' _ => by by_cases h : w' = g <;> simp [h, hnn]) (Finset.mem_univ w)
  have h2 : (∑ w', if w' = g then 0 else J g w') ≤ errorProb J :=
    Finset.single_le_sum (f := fun g' => ∑ w', if w' = g' then 0 else J g' w')
      (fun g' _ => hrownn g') (Finset.mem_univ g)
  rw [if_neg hwg] at h1
  linarith

/-! ## The cellwise Gibbs step -/

/-- Comparing a cell against any positive comparison mass costs at most the
difference of masses.  This is `log x ≤ x - 1` in the form the guarded sums
need. -/
theorem gibbs_cell {j p q : ℝ} (hj : 0 ≤ j) (hjp : j ≤ p) (hq : 0 ≤ q)
    (hjq : j ≠ 0 → 0 < q) :
    (if j = 0 then 0 else j * Real.log (p / j))
      ≤ (if j = 0 then 0 else j * Real.log (p / q)) + (q - j) := by
  by_cases hz : j = 0
  · simp [hz, hq]
  · have hjpos : 0 < j := lt_of_le_of_ne hj (Ne.symm hz)
    have hppos : 0 < p := lt_of_lt_of_le hjpos hjp
    have hqpos : 0 < q := hjq hz
    simp only [hz, if_false]
    have hlog : Real.log (q / j) ≤ q / j - 1 :=
      Real.log_le_sub_one_of_pos (by positivity)
    have key : j * Real.log (p / j) - j * Real.log (p / q)
        = j * Real.log (q / j) := by
      rw [Real.log_div hppos.ne' hjpos.ne', Real.log_div hppos.ne' hqpos.ne',
        Real.log_div hqpos.ne' hjpos.ne']
      ring
    have hmul : j * Real.log (q / j) ≤ j * (q / j - 1) :=
      mul_le_mul_of_nonneg_left hlog hj
    have hfin : j * (q / j - 1) = q - j := by field_simp
    linarith

/-- Rewriting the off-diagonal comparison term into binary-entropy form. -/
theorem errorProb_log_split {e m : ℝ} (he : 0 ≤ e) (hm : 0 < m) :
    e * Real.log (e / m)⁻¹ = shannon e + e * Real.log m := by
  by_cases hz : e = 0
  · simp [hz]
  · have hepos : 0 < e := lt_of_le_of_ne he (Ne.symm hz)
    unfold shannon
    rw [inv_div, Real.log_div hm.ne' hepos.ne', Real.log_inv]
    ring

/-! ## Fano's inequality -/

/-- Weight the comparison law puts on answer `w` when the guess is `g`: the
correct-answer mass on the guess itself, and `Pe / M` on every answer.  Its
rows sum to at most one, which is all Gibbs' inequality needs. -/
def fanoWeight (J : γ → γ → ℝ) (g w : γ) : ℝ :=
  if w = g then correctProb J else errorProb J / (Fintype.card γ : ℝ)

/-- The comparison law: the guess marginal times the weight. -/
def fanoComparison (J : γ → γ → ℝ) (g w : γ) : ℝ :=
  fstMarginal J g * fanoWeight J g w

/-- **Fano's inequality.**  If the guess is usually right then little
uncertainty about the truth survives knowing the guess.  Here
`H(truth ∣ guess)` is `condEntropy J` for a joint law `J` whose first
argument is the guess. -/
theorem fano {J : γ → γ → ℝ} (hnn : ∀ g w, 0 ≤ J g w)
    (hsum : ∑ g, ∑ w, J g w = 1) :
    condEntropy J
      ≤ shannon (correctProb J) + shannon (errorProb J)
        + errorProb J * Real.log (Fintype.card γ) := by
  have hne : Nonempty γ := by
    by_contra h
    rw [not_nonempty_iff] at h
    simp at hsum
  have hM : (0 : ℝ) < (Fintype.card γ : ℝ) := by exact_mod_cast Fintype.card_pos
  have hPcnn : 0 ≤ correctProb J := correctProb_nonneg hnn
  have hPenn : 0 ≤ errorProb J := errorProb_nonneg hnn
  have hpnn : ∀ g : γ, 0 ≤ fstMarginal J g := fun g =>
    Finset.sum_nonneg fun w _ => hnn g w
  have hJp : ∀ g w, J g w ≤ fstMarginal J g := fun g w =>
    Finset.single_le_sum (f := fun w => J g w) (fun w _ => hnn g w)
      (Finset.mem_univ w)
  have hpc : correctProb J + errorProb J = 1 := by
    rw [correct_add_error]; exact hsum
  have hwnn : ∀ g w, 0 ≤ fanoWeight J g w := by
    intro g w
    unfold fanoWeight
    by_cases h : w = g
    · simpa [h] using hPcnn
    · have hd : (0 : ℝ) ≤ errorProb J / (Fintype.card γ : ℝ) := by positivity
      simpa [h] using hd
  have hQnn : ∀ g w, 0 ≤ fanoComparison J g w := fun g w =>
    mul_nonneg (hpnn g) (hwnn g w)
  have hwpos : ∀ g w, J g w ≠ 0 → 0 < fanoWeight J g w := by
    intro g w hz
    have hjpos : 0 < J g w := lt_of_le_of_ne (hnn g w) (Ne.symm hz)
    unfold fanoWeight
    by_cases h : w = g
    · subst h
      have hle := le_correctProb hnn w
      rw [if_pos rfl]
      linarith
    · rw [if_neg h]
      have hle := le_errorProb hnn h
      have hepos : 0 < errorProb J := lt_of_lt_of_le hjpos hle
      positivity
  have hQpos : ∀ g w, J g w ≠ 0 → 0 < fanoComparison J g w := by
    intro g w hz
    have hjpos : 0 < J g w := lt_of_le_of_ne (hnn g w) (Ne.symm hz)
    exact mul_pos (lt_of_lt_of_le hjpos (hJp g w)) (hwpos g w hz)
  have hrow : ∀ g : γ, ∑ w, fanoComparison J g w ≤ fstMarginal J g := by
    intro g
    have hdnn : (0 : ℝ) ≤ fstMarginal J g * (errorProb J / (Fintype.card γ : ℝ)) := by
      have := hpnn g
      positivity
    have hstep : ∀ w ∈ (Finset.univ : Finset γ),
        fanoComparison J g w
          ≤ fstMarginal J g * (if w = g then correctProb J else 0)
            + fstMarginal J g * (errorProb J / (Fintype.card γ : ℝ)) := by
      intro w _
      unfold fanoComparison fanoWeight
      by_cases h : w = g
      · rw [if_pos h, if_pos h]
        linarith
      · rw [if_neg h, if_neg h, mul_zero, zero_add]
    have he1 : ∑ w : γ, fstMarginal J g * (if w = g then correctProb J else 0)
        = fstMarginal J g * correctProb J := by
      rw [← Finset.mul_sum,
        Finset.sum_ite_eq' Finset.univ g (fun _ : γ => correctProb J)]
      simp
    have he2 : ∑ _w : γ, fstMarginal J g * (errorProb J / (Fintype.card γ : ℝ))
        = fstMarginal J g * errorProb J := by
      rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
      field_simp
    have hle := Finset.sum_le_sum hstep
    rw [Finset.sum_add_distrib, he1, he2] at hle
    calc ∑ w, fanoComparison J g w
        ≤ fstMarginal J g * correctProb J + fstMarginal J g * errorProb J := hle
      _ = fstMarginal J g := by rw [← mul_add, hpc, mul_one]
  have hQsum : ∑ g, ∑ w, fanoComparison J g w ≤ 1 := by
    calc ∑ g, ∑ w, fanoComparison J g w
        ≤ ∑ g, fstMarginal J g := Finset.sum_le_sum fun g _ => hrow g
      _ = 1 := by rw [sum_fstMarginal]; exact hsum
  have hX : ∀ g w,
      (if J g w = 0 then 0
        else J g w * Real.log (fstMarginal J g / fanoComparison J g w))
        = J g w * Real.log (fanoWeight J g w)⁻¹ := by
    intro g w
    by_cases hz : J g w = 0
    · simp [hz]
    · have hjpos : 0 < J g w := lt_of_le_of_ne (hnn g w) (Ne.symm hz)
      have hppos : 0 < fstMarginal J g := lt_of_lt_of_le hjpos (hJp g w)
      have hcp : 0 < fanoWeight J g w := hwpos g w hz
      rw [if_neg hz]
      unfold fanoComparison
      rw [show fstMarginal J g / (fstMarginal J g * fanoWeight J g w)
            = (fanoWeight J g w)⁻¹ by field_simp]
  have hXsum : ∑ g, ∑ w, J g w * Real.log (fanoWeight J g w)⁻¹
      = shannon (correctProb J)
        + errorProb J * Real.log (errorProb J / (Fintype.card γ : ℝ))⁻¹ := by
    have hrowsplit : ∀ g ∈ (Finset.univ : Finset γ),
        ∑ w, J g w * Real.log (fanoWeight J g w)⁻¹
          = J g g * Real.log (correctProb J)⁻¹
            + ∑ w, (if w = g then 0 else J g w)
                * Real.log (errorProb J / (Fintype.card γ : ℝ))⁻¹ := by
      intro g _
      have hsplit : ∀ w ∈ (Finset.univ : Finset γ),
          J g w * Real.log (fanoWeight J g w)⁻¹
            = (if w = g then J g w * Real.log (correctProb J)⁻¹ else 0)
              + (if w = g then 0 else J g w)
                * Real.log (errorProb J / (Fintype.card γ : ℝ))⁻¹ := by
        intro w _
        unfold fanoWeight
        by_cases h : w = g <;> simp [h]
      rw [Finset.sum_congr rfl hsplit, Finset.sum_add_distrib,
        Finset.sum_ite_eq' Finset.univ g
          (fun w => J g w * Real.log (correctProb J)⁻¹)]
      simp
    have h1 : ∑ g : γ, J g g * Real.log (correctProb J)⁻¹
        = shannon (correctProb J) := by
      unfold shannon correctProb
      rw [Finset.sum_mul]
    have h2 : ∑ g : γ, ∑ w : γ, (if w = g then 0 else J g w)
          * Real.log (errorProb J / (Fintype.card γ : ℝ))⁻¹
        = errorProb J * Real.log (errorProb J / (Fintype.card γ : ℝ))⁻¹ := by
      unfold errorProb
      rw [Finset.sum_mul]
      exact Finset.sum_congr rfl fun g _ => (Finset.sum_mul _ _ _).symm
    rw [Finset.sum_congr rfl hrowsplit, Finset.sum_add_distrib, h1, h2]
  have hbound : condEntropy J
      ≤ (∑ g, ∑ w, J g w * Real.log (fanoWeight J g w)⁻¹)
        + (∑ g, ∑ w, fanoComparison J g w) - 1 := by
    unfold condEntropy
    have hcellsum : ∑ g, ∑ w,
        (if J g w = 0 then 0 else J g w * Real.log (fstMarginal J g / J g w))
          ≤ ∑ g, ∑ w,
              ((if J g w = 0 then 0
                else J g w * Real.log (fstMarginal J g / fanoComparison J g w))
                + (fanoComparison J g w - J g w)) :=
      Finset.sum_le_sum fun g _ => Finset.sum_le_sum fun w _ =>
        gibbs_cell (hnn g w) (hJp g w) (hQnn g w) (hQpos g w)
    have hrhs : ∑ g, ∑ w,
        ((if J g w = 0 then 0
          else J g w * Real.log (fstMarginal J g / fanoComparison J g w))
          + (fanoComparison J g w - J g w))
        = (∑ g, ∑ w, J g w * Real.log (fanoWeight J g w)⁻¹)
          + (∑ g, ∑ w, fanoComparison J g w) - 1 := by
      have hstep : ∀ g ∈ (Finset.univ : Finset γ), ∑ w,
          ((if J g w = 0 then 0
            else J g w * Real.log (fstMarginal J g / fanoComparison J g w))
            + (fanoComparison J g w - J g w))
          = (∑ w, J g w * Real.log (fanoWeight J g w)⁻¹)
            + (∑ w, fanoComparison J g w) - (∑ w, J g w) := by
        intro g _
        have hin : ∑ w, (if J g w = 0 then 0
              else J g w * Real.log (fstMarginal J g / fanoComparison J g w))
            = ∑ w, J g w * Real.log (fanoWeight J g w)⁻¹ :=
          Finset.sum_congr rfl fun w _ => hX g w
        rw [Finset.sum_add_distrib, Finset.sum_sub_distrib, hin]
        ring
      rw [Finset.sum_congr rfl hstep, Finset.sum_sub_distrib,
        Finset.sum_add_distrib, hsum]
    linarith [hcellsum, hrhs.ge, hrhs.le]
  rw [hXsum, errorProb_log_split hPenn hM] at hbound
  linarith [hbound, hQsum]

section Verification

#print axioms correct_add_error
#print axioms gibbs_cell
#print axioms fano

end Verification

end

end TranscendenceTower.FiniteInformation
