/-
Definitions for the weak converse: words, product laws, memoryless channels,
and the guess/truth quantities Fano's inequality is stated in.

This imports the generic finite-information bundle and adds only the
constructions needed to talk about repeated use of a channel and about a
decoder that may be wrong.

Definitions only; every claim about these objects is proved in the theorem
that imports this bundle.
-/

import Definitions.Def_TranscendenceTowerFiniteInformation

set_option autoImplicit false

open scoped BigOperators
open TranscendenceTower.FiniteInformation

namespace TranscendenceTower.ConversePlatform

noncomputable section

variable {α β γ : Type} [Fintype α] [DecidableEq α] [Fintype β] [DecidableEq β]

/-! ## Words -/

/-- Words of length `n+1` are prefixes of length `n` paired with a last
symbol. -/
def snocEquiv (n : ℕ) : ((Fin n → β) × β) ≃ (Fin (n + 1) → β) where
  toFun p := Fin.snoc p.1 p.2
  invFun w := (Fin.init w, w (Fin.last n))
  left_inv p := by simp
  right_inv w := by simp

/-- A law on words of length `n+1`, read as a joint law on
(prefix, last symbol). -/
def splitLast {n : ℕ} (law : (Fin (n + 1) → β) → ℝ) : (Fin n → β) → β → ℝ :=
  fun w b => law (Fin.snoc w b)

/-- The `i`-th coordinate marginal of a law on words. -/
def coordMarginal {n : ℕ} (law : (Fin n → β) → ℝ) (i : Fin n) : β → ℝ :=
  fun b => ∑ w : Fin n → β, if w i = b then law w else 0

/-- The product law on words induced by a family of per-coordinate laws. -/
def productLaw {n : ℕ} (rows : Fin n → β → ℝ) : (Fin n → β) → ℝ :=
  fun w => ∏ i, rows i (w i)

/-- The word-level joint law of an input prior and a memoryless channel:
draw an input word from the prior, then pass it through the channel
coordinatewise and independently. -/
def channelJoint {n : ℕ} (prior : (Fin n → α) → ℝ) (K : α → β → ℝ) :
    (Fin n → α) → (Fin n → β) → ℝ :=
  fun x y => prior x * productLaw (fun i => K (x i)) y

/-! ## Guess and truth -/

variable [Fintype γ] [DecidableEq γ]

/-- Probability that the guess equals the truth. -/
def correctProb (J : γ → γ → ℝ) : ℝ := ∑ g, J g g

/-- Probability that the guess differs from the truth. -/
def errorProb (J : γ → γ → ℝ) : ℝ := ∑ g, ∑ w, if w = g then 0 else J g w

/-- Weight the comparison law used in Fano's inequality puts on answer `w`
when the guess is `g`: the correct-answer mass on the guess itself, and
`Pe / M` on every answer.  Its rows sum to at most one. -/
def fanoWeight (J : γ → γ → ℝ) (g w : γ) : ℝ :=
  if w = g then correctProb J else errorProb J / (Fintype.card γ : ℝ)

/-- The comparison law: the guess marginal times the weight. -/
def fanoComparison (J : γ → γ → ℝ) (g w : γ) : ℝ :=
  fstMarginal J g * fanoWeight J g w

end

end TranscendenceTower.ConversePlatform
