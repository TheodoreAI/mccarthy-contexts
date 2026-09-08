/-
Generic finite Shannon information theory over arbitrary finite alphabets.

Mathlib supplies `Real.binEntropy` and a measure-theoretic Kullback-Leibler
divergence, but no discrete entropy, conditional entropy or mutual information.
This bundle supplies them over any `Fintype`, as plain finite sums in nats,
with zero-mass cells contributing zero by convention.

Definitions only; every claim about these objects is proved in the theorem
that imports this bundle.
-/

import Mathlib.Analysis.SpecialFunctions.BinaryEntropy
import Mathlib.Analysis.MeanInequalities

set_option autoImplicit false

open scoped BigOperators

namespace TranscendenceTower.FiniteInformation

noncomputable section

variable {α β : Type} [Fintype α] [Fintype β]

/-- A finite mass function is a distribution when it is nonnegative and sums
to one. -/
def IsDist (mass : α → ℝ) : Prop :=
  (∀ x, 0 ≤ mass x) ∧ ∑ x, mass x = 1

/-- The Shannon summand, in nats, with the standard `0 log 0 = 0` convention
supplied by `Real.log 0 = 0`. -/
def shannon (p : ℝ) : ℝ := p * Real.log p⁻¹

@[simp] theorem shannon_zero : shannon (0 : ℝ) = 0 := by simp [shannon]

@[simp] theorem shannon_one : shannon (1 : ℝ) = 0 := by simp [shannon]

/-- Shannon entropy of a finite mass function, in nats. -/
def entropy (mass : α → ℝ) : ℝ := ∑ x, shannon (mass x)

/-- The first marginal of a joint law. -/
def fstMarginal (joint : α → β → ℝ) : α → ℝ := fun a => ∑ b, joint a b

/-- The second marginal of a joint law. -/
def sndMarginal (joint : α → β → ℝ) : β → ℝ := fun b => ∑ a, joint a b

/-- Joint entropy of a law on `α × β`. -/
def jointEntropy (joint : α → β → ℝ) : ℝ :=
  ∑ a, ∑ b, shannon (joint a b)

/-- Conditional entropy `H(β ∣ α)`, as the joint sum
`∑ p(a,b) log (p(a) / p(a,b))`.  Cells of zero mass contribute zero. -/
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

end

end TranscendenceTower.FiniteInformation
