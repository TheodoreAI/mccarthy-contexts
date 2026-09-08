import Definitions.Def_TranscendenceTowerZeroError

set_option autoImplicit false

open scoped BigOperators
open TranscendenceTower TranscendenceTower.ContextTheories
  TranscendenceTower.Lifting
open TranscendenceTower.InformationTheoryPlatform
open TranscendenceTower.InformationTheoryCapacityPlatform
open TranscendenceTower.ZeroErrorPlatform

/-- Both routes admit survival, so no single observation distinguishes them. -/
private theorem ze_routeChannel_true_pos (r : Route) : 0 < routeChannel r true := by
  cases r <;> norm_num [routeChannel]

/-- The all-survive word is possible under every input word.  This single
observation is what kills zero-error coding: the channel has no output that
rules any input out. -/
private theorem ze_allSurvive_possible (n : ℕ) (x : Fin n → Route) :
    Possible n x (allSurvive n) :=
  Finset.prod_pos fun i _ => ze_routeChannel_true_pos (x i)

/-- No zero-error code carries more than one message, at any blocklength. -/
private theorem ze_subsingleton {n M : ℕ} (c : ZeroErrorCode n M) : M ≤ 1 := by
  by_contra hM
  push Not at hM
  have h0 : c.dec (allSurvive n) = (⟨0, by omega⟩ : Fin M) :=
    c.correct _ _ (ze_allSurvive_possible n _)
  have h1 : c.dec (allSurvive n) = (⟨1, by omega⟩ : Fin M) :=
    c.correct _ _ (ze_allSurvive_possible n _)
  have hcontra : (⟨0, by omega⟩ : Fin M) = ⟨1, by omega⟩ := h0.symm.trans h1
  simp [Fin.ext_iff] at hcontra

/-- Consequently every zero-error code has rate `0` nats per use. -/
private theorem ze_rate_zero {n M : ℕ} (c : ZeroErrorCode n M) :
    codeRate n M = 0 := by
  have hM : M = 0 ∨ M = 1 := by
    have := ze_subsingleton c
    omega
  rcases hM with rfl | rfl <;> simp [codeRate]

/-- A one-message zero-error code exists, so the bound `M ≤ 1` is attained
rather than vacuous. -/
private def ze_trivialCode (n : ℕ) : ZeroErrorCode n 1 where
  enc := fun _ _ => Route.direct
  dec := fun _ => 0
  correct := by intro m _ _; exact Subsingleton.elim _ _

/-- The zero-error capacity of the route/survival channel is `0`, while its
one-use maximum `log (5/4)` is strictly positive. -/
theorem solution :
    (∀ n M : ℕ, ZeroErrorCode n M → M ≤ 1 ∧ codeRate n M = 0)
      ∧ (∀ n : ℕ, Nonempty (ZeroErrorCode n 1))
      ∧ (∀ (n : ℕ) (x : Fin n → Route), Possible n x (allSurvive n))
      ∧ 0 < Real.log (5 / 4) :=
  ⟨fun _ _ c => ⟨ze_subsingleton c, ze_rate_zero c⟩,
    fun n => ⟨ze_trivialCode n⟩,
    ze_allSurvive_possible,
    Real.log_pos (by norm_num)⟩

#print axioms solution
