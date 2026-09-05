import Definitions.Def_TranscendenceTowerReification

set_option autoImplicit false

open TranscendenceTower TranscendenceTower.Reification

/-- The canonical expansion satisfies the Tarski schema, by construction. -/
theorem satT0_expand' (v : Val) : SatT0 (expand v) := fun _ => Iff.rfl

theorem solution :
    (∃ M : RStruc, SatT0 M) ∧ (∀ v : Val, ∃ M : RStruc, SatT0 M ∧ M.val = v) :=
  ⟨⟨expand (fun _ => false), satT0_expand' _⟩,
   fun v => ⟨expand v, satT0_expand' v, rfl⟩⟩
