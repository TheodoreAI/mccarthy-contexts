/-
  The weak converse.

  Fano's inequality bounds the uncertainty that survives a guess; mutual
  information bounds what the guess could have been based on.  Together they
  say that the entropy of what you are trying to recover cannot exceed the
  information you actually have, plus a term that vanishes as the error
  probability goes to zero.

  Specialized to a uniform truth over `M` possibilities, this is the familiar
  rate bound: `(1 - Pe) log M ≤ I + h(Pe)`.  An auditor who is usually right
  can only have been distinguishing about `exp I` histories.

  The `bound` on mutual information is left as a hypothesis rather than
  hard-wired.  For a memoryless channel it is discharged by
  `mutualInfo_channelJoint_le`, which gives the single-letter `n`-use bound.
  See the note at the end of this file on what that instantiation still needs.
-/

import Development.Fano

set_option autoImplicit false

open scoped BigOperators

namespace TranscendenceTower.FiniteInformation

noncomputable section

variable {γ : Type} [Fintype γ] [DecidableEq γ]

/-! ## The weak converse -/

/-- **Weak converse.**  If the information a guess carries about the truth is
at most `bound`, and the guess errs with probability `Pe`, then the truth
cannot have carried much more entropy than `bound`: the excess is at most the
binary entropy of the error plus `Pe log M`. -/
theorem weak_converse {J : γ → γ → ℝ} (hnn : ∀ g w, 0 ≤ J g w)
    (hsum : ∑ g, ∑ w, J g w = 1) {bound : ℝ} (hI : mutualInfo J ≤ bound) :
    entropy (sndMarginal J)
      ≤ bound + shannon (correctProb J) + shannon (errorProb J)
        + errorProb J * Real.log (Fintype.card γ) := by
  have hfano := fano hnn hsum
  have hsplit := mutualInfo_eq_sub_condEntropy hnn
  linarith

/-- **The rate bound.**  When the truth is uniform over `M` possibilities, the
weak converse reads `(1 - Pe) log M ≤ bound + h(Pe)`.  Dividing by the number
of channel uses turns this into the statement that no rate above capacity is
achievable with vanishing error. -/
theorem weak_converse_uniform {J : γ → γ → ℝ} (hnn : ∀ g w, 0 ≤ J g w)
    (hsum : ∑ g, ∑ w, J g w = 1) {bound : ℝ} (hI : mutualInfo J ≤ bound)
    (huniform : entropy (sndMarginal J) = Real.log (Fintype.card γ)) :
    (1 - errorProb J) * Real.log (Fintype.card γ)
      ≤ bound + shannon (correctProb J) + shannon (errorProb J) := by
  have h := weak_converse hnn hsum hI
  rw [huniform] at h
  rw [sub_mul, one_mul]
  linarith

/-- The same bound with the error terms named, in the shape a rate argument
uses: the recoverable entropy is capped by the information plus a penalty that
vanishes with the error probability. -/
theorem recoverable_entropy_le {J : γ → γ → ℝ} (hnn : ∀ g w, 0 ≤ J g w)
    (hsum : ∑ g, ∑ w, J g w = 1) {bound : ℝ} (hI : mutualInfo J ≤ bound)
    (huniform : entropy (sndMarginal J) = Real.log (Fintype.card γ))
    (hPe : errorProb J < 1) :
    Real.log (Fintype.card γ)
      ≤ (bound + shannon (correctProb J) + shannon (errorProb J))
          / (1 - errorProb J) := by
  have h := weak_converse_uniform hnn hsum hI huniform
  have hpos : 0 < 1 - errorProb J := by linarith
  rw [le_div_iff₀ hpos]
  linarith [h]

/-! ## Non-vacuity

The hypotheses are satisfiable: a guess that is always right has error
probability zero, and then the bound says exactly that the truth's entropy is
at most the information carried about it. -/

/-- A perfectly correlated law: the guess always equals the truth. -/
def diagonalLaw (p : γ → ℝ) : γ → γ → ℝ :=
  fun g w => if w = g then p g else 0

theorem diagonalLaw_nonneg {p : γ → ℝ} (hp : ∀ g, 0 ≤ p g) (g w : γ) :
    0 ≤ diagonalLaw p g w := by
  unfold diagonalLaw
  by_cases h : w = g <;> simp [h, hp]

theorem sum_diagonalLaw (p : γ → ℝ) :
    ∑ g, ∑ w, diagonalLaw p g w = ∑ g, p g := by
  refine Finset.sum_congr rfl fun g _ => ?_
  unfold diagonalLaw
  rw [Finset.sum_ite_eq' Finset.univ g (fun _ : γ => p g)]
  simp

/-- A perfect guess has error probability zero, so the penalty terms vanish
and the weak converse is not vacuous. -/
theorem errorProb_diagonalLaw (p : γ → ℝ) : errorProb (diagonalLaw p) = 0 := by
  unfold errorProb diagonalLaw
  refine Finset.sum_eq_zero fun g _ => Finset.sum_eq_zero fun w _ => ?_
  by_cases h : w = g <;> simp [h]

section Verification

#print axioms weak_converse
#print axioms weak_converse_uniform
#print axioms recoverable_entropy_le
#print axioms errorProb_diagonalLaw

end Verification

end

end TranscendenceTower.FiniteInformation
