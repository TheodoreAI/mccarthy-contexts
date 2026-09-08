/-
  Zero-error coding for the route/survival channel.

  The companion capacity development shows that the channel has positive
  Shannon capacity, `log (5/4)` nats.  This module shows that its *zero-error*
  capacity is `0`: no block code of any length carries more than one message
  without the possibility of error.

  The two facts together say that route information is available on average
  but never with certainty.  Nothing here is asymptotic; the argument is finite
  combinatorics on the support of the product channel.
-/

import Development.InformationTheory

set_option autoImplicit false

open scoped BigOperators
open TranscendenceTower TranscendenceTower.ContextTheories
  TranscendenceTower.Lifting

namespace TranscendenceTower.InformationTheory

noncomputable section

/-! ## Codes that are never wrong -/

/-- `y` is a possible observation when the input word `x` is transmitted:
the product channel assigns it positive mass. -/
def Possible (n : ℕ) (x : Fin n → Route) (y : Fin n → Bool) : Prop :=
  0 < blockChannel n x y

/-- A block code of length `n` carrying `M` messages whose decoder is never
wrong: every output word that can actually arise from codeword `m` is decoded
back to `m`.  No probability is involved — this is a support condition. -/
structure ZeroErrorCode (n M : ℕ) where
  /-- The encoder, sending each message to an input word. -/
  enc : Fin M → (Fin n → Route)
  /-- The decoder, reading an output word back to a message. -/
  dec : (Fin n → Bool) → Fin M
  /-- Correctness on the whole support of each codeword. -/
  correct : ∀ m y, Possible n (enc m) y → dec y = m

/-- Rate of a length-`n`, size-`M` block code, in nats per channel use. -/
def codeRate (n M : ℕ) : ℝ := Real.log M / n

/-! ## Every input word can produce total survival -/

/-- Both routes admit survival, so no output symbol distinguishes them with
certainty. -/
theorem routeChannel_true_pos (r : Route) : 0 < routeChannel r true := by
  cases r <;> norm_num [routeChannel]

/-- The output word on which every fact survives. -/
def allSurvive (n : ℕ) : Fin n → Bool := fun _ => true

/-- The all-survive word is possible under *every* input word.  This single
observation is what kills zero-error coding: the channel has no output that
rules any input out. -/
theorem allSurvive_possible (n : ℕ) (x : Fin n → Route) :
    Possible n x (allSurvive n) :=
  Finset.prod_pos fun i _ => routeChannel_true_pos (x i)

/-! ## The zero-error capacity is zero -/

/-- **No zero-error code carries more than one message**, at any blocklength.
Every codeword can produce the all-survive word, so a decoder that is never
wrong must return the same message for all of them. -/
theorem zeroErrorCode_subsingleton {n M : ℕ} (c : ZeroErrorCode n M) : M ≤ 1 := by
  by_contra hM
  push Not at hM
  have h0 : c.dec (allSurvive n) = (⟨0, by omega⟩ : Fin M) :=
    c.correct _ _ (allSurvive_possible n _)
  have h1 : c.dec (allSurvive n) = (⟨1, by omega⟩ : Fin M) :=
    c.correct _ _ (allSurvive_possible n _)
  have hcontra : (⟨0, by omega⟩ : Fin M) = ⟨1, by omega⟩ := h0.symm.trans h1
  simp [Fin.ext_iff] at hcontra

/-- Consequently every zero-error code has rate `0` nats per use. -/
theorem zeroErrorCode_rate_zero {n M : ℕ} (c : ZeroErrorCode n M) :
    codeRate n M = 0 := by
  have hM : M = 0 ∨ M = 1 := by
    have := zeroErrorCode_subsingleton c
    omega
  rcases hM with rfl | rfl <;> simp [codeRate]

/-- Non-vacuity: a one-message zero-error code does exist, so the bound
`M ≤ 1` is attained rather than empty. -/
def trivialZeroErrorCode (n : ℕ) : ZeroErrorCode n 1 where
  enc := fun _ _ => Route.direct
  dec := fun _ => 0
  correct := by intro m _ _; exact Subsingleton.elim _ _

/-- **The headline gap.** The channel has zero-error capacity `0` — no code of
any length transmits even one bit with certainty — while its Shannon capacity
`log (5/4)` is strictly positive.  Route information is available on average
and never with certainty. -/
theorem zero_error_capacity_zero_lt_shannon_capacity :
    (∀ n M : ℕ, ZeroErrorCode n M → M ≤ 1 ∧ codeRate n M = 0)
      ∧ (∀ n : ℕ, Nonempty (ZeroErrorCode n 1))
      ∧ 0 < Real.log (5 / 4) :=
  ⟨fun _ _ c => ⟨zeroErrorCode_subsingleton c, zeroErrorCode_rate_zero c⟩,
    fun n => ⟨trivialZeroErrorCode n⟩,
    Real.log_pos (by norm_num)⟩

section Verification

#print axioms allSurvive_possible
#print axioms zeroErrorCode_subsingleton
#print axioms zeroErrorCode_rate_zero
#print axioms zero_error_capacity_zero_lt_shannon_capacity

end Verification

end

end TranscendenceTower.InformationTheory
