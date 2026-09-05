import Definitions.Def_TranscendenceTowerReification

set_option autoImplicit false

open TranscendenceTower TranscendenceTower.Reification

theorem solution : ∀ (S S' : Set L0), S ≠ S' →
    ¬ ∃ M : RStruc, SatT0 M ∧ SatCL M S ∧ SatCL M S' := by
  rintro S S' h ⟨M, _, hS, hS'⟩
  exact h (Set.ext fun p => (hS p).symm.trans (hS' p))
