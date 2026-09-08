/-
  Information theory on words: the independence bound.

  `H(Y_1,\dots,Y_n) \le \sum_i H(Y_i)` for any law on words of length `n`.

  The proof is an induction that peels the last coordinate off a word,
  turning a law on `Fin (n+1) → β` into a two-variable joint law on
  (prefix, last symbol).  That reduces each step to the ordinary two-variable
  subadditivity already proved, so no conditional mutual information and no
  `n`-fold chain rule are required.
-/

import Development.FiniteInformation

set_option autoImplicit false

open scoped BigOperators

namespace TranscendenceTower.FiniteInformation

noncomputable section

variable {β : Type} [Fintype β] [DecidableEq β]

/-! ## Peeling the last coordinate -/

/-- Words of length `n+1` are prefixes of length `n` paired with a last
symbol. -/
def snocEquiv (n : ℕ) : ((Fin n → β) × β) ≃ (Fin (n + 1) → β) where
  toFun p := Fin.snoc p.1 p.2
  invFun w := (Fin.init w, w (Fin.last n))
  left_inv p := by simp
  right_inv w := by simp

/-- A sum over words of length `n+1` splits as a sum over prefixes and last
symbols. -/
theorem sum_snoc {n : ℕ} (f : (Fin (n + 1) → β) → ℝ) :
    ∑ w : Fin (n + 1) → β, f w
      = ∑ w : Fin n → β, ∑ b : β, f (Fin.snoc w b) := by
  have h : ∑ p : (Fin n → β) × β, f (Fin.snoc p.1 p.2)
      = ∑ w : Fin (n + 1) → β, f w :=
    Fintype.sum_equiv (snocEquiv n) _ _ (fun _ => rfl)
  rw [← h, Fintype.sum_prod_type]

/-- A law on words of length `n+1`, read as a joint law on
(prefix, last symbol). -/
def splitLast {n : ℕ} (law : (Fin (n + 1) → β) → ℝ) : (Fin n → β) → β → ℝ :=
  fun w b => law (Fin.snoc w b)

/-- The `i`-th coordinate marginal of a law on words. -/
def coordMarginal {n : ℕ} (law : (Fin n → β) → ℝ) (i : Fin n) : β → ℝ :=
  fun b => ∑ w : Fin n → β, if w i = b then law w else 0

/-! ## Identifying the marginals of the split -/

/-- The last-symbol marginal of the split is the last coordinate marginal. -/
theorem sndMarginal_splitLast {n : ℕ} (law : (Fin (n + 1) → β) → ℝ) :
    sndMarginal (splitLast law) = coordMarginal law (Fin.last n) := by
  funext b
  unfold sndMarginal coordMarginal splitLast
  rw [sum_snoc]
  refine Finset.sum_congr rfl fun w _ => ?_
  simp [Fin.snoc_last]

/-- Marginalizing out the last symbol commutes with taking an earlier
coordinate marginal. -/
theorem coordMarginal_fstMarginal_splitLast {n : ℕ}
    (law : (Fin (n + 1) → β) → ℝ) (i : Fin n) :
    coordMarginal (fstMarginal (splitLast law)) i
      = coordMarginal law i.castSucc := by
  funext b
  unfold coordMarginal fstMarginal splitLast
  rw [sum_snoc]
  refine Finset.sum_congr rfl fun w _ => ?_
  by_cases h : w i = b
  · simp [h]
  · simp [h]

/-! ## Nonnegativity and normalization pass to the split -/

theorem splitLast_nonneg {n : ℕ} {law : (Fin (n + 1) → β) → ℝ}
    (hnn : ∀ w, 0 ≤ law w) (w : Fin n → β) (b : β) : 0 ≤ splitLast law w b :=
  hnn _

theorem splitLast_sum {n : ℕ} {law : (Fin (n + 1) → β) → ℝ}
    (hsum : ∑ w, law w = 1) :
    ∑ w : Fin n → β, ∑ b : β, splitLast law w b = 1 := by
  unfold splitLast
  rw [← sum_snoc]
  exact hsum

theorem fstMarginal_splitLast_nonneg {n : ℕ} {law : (Fin (n + 1) → β) → ℝ}
    (hnn : ∀ w, 0 ≤ law w) (w : Fin n → β) :
    0 ≤ fstMarginal (splitLast law) w :=
  Finset.sum_nonneg fun b _ => splitLast_nonneg hnn w b

theorem fstMarginal_splitLast_sum {n : ℕ} {law : (Fin (n + 1) → β) → ℝ}
    (hsum : ∑ w, law w = 1) :
    ∑ w : Fin n → β, fstMarginal (splitLast law) w = 1 :=
  splitLast_sum hsum

/-! ## The independence bound -/

/-- **Independence bound on entropy.**  A law on words of length `n` has
entropy at most the sum of the entropies of its coordinate marginals.
Equality would say the coordinates are independent; the inequality holds
always. -/
theorem entropy_le_sum_coordMarginal :
    ∀ (n : ℕ) (law : (Fin n → β) → ℝ), (∀ w, 0 ≤ law w) → (∑ w, law w = 1) →
      entropy law ≤ ∑ i : Fin n, entropy (coordMarginal law i) := by
  intro n
  induction n with
  | zero =>
    intro law _ hsum
    rw [Finset.univ_unique, Finset.sum_singleton] at hsum
    unfold entropy
    rw [Finset.univ_unique, Finset.sum_singleton, hsum, shannon_one]
    simp
  | succ n ih =>
    intro law hnn hsum
    have hjn : ∀ w b, 0 ≤ splitLast law w b := splitLast_nonneg hnn
    have hjs : ∑ w : Fin n → β, ∑ b : β, splitLast law w b = 1 :=
      splitLast_sum hsum
    -- The entropy of the word law is the joint entropy of the split.
    have hsplit : entropy law = jointEntropy (splitLast law) := by
      unfold entropy jointEntropy splitLast
      exact sum_snoc _
    -- Two-variable subadditivity at this level.
    have hsub := jointEntropy_le_add hjn hjs
    -- The inductive hypothesis, applied to the prefix law.
    have hih := ih (fstMarginal (splitLast law))
      (fstMarginal_splitLast_nonneg hnn) (fstMarginal_splitLast_sum hsum)
    rw [hsplit]
    have hlast : entropy (sndMarginal (splitLast law))
        = entropy (coordMarginal law (Fin.last n)) := by
      rw [sndMarginal_splitLast]
    have hrest : ∑ i : Fin n, entropy (coordMarginal (fstMarginal (splitLast law)) i)
        = ∑ i : Fin n, entropy (coordMarginal law i.castSucc) :=
      Finset.sum_congr rfl fun i _ => by
        rw [coordMarginal_fstMarginal_splitLast]
    rw [hrest] at hih
    rw [Fin.sum_univ_castSucc]
    linarith [hsub, hih, hlast.ge, hlast.le]

section Verification

#print axioms sum_snoc
#print axioms sndMarginal_splitLast
#print axioms coordMarginal_fstMarginal_splitLast
#print axioms entropy_le_sum_coordMarginal

end Verification

end

end TranscendenceTower.FiniteInformation
