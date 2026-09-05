import Definitions.Def_TranscendenceTowerLifting

set_option autoImplicit false

open TranscendenceTower TranscendenceTower.ContextTheories TranscendenceTower.Lifting

theorem cn_mono' {T T' : Set L0} (h : T ⊆ T') : Cn T ⊆ Cn T' :=
  fun _ hp v hv => hp v (fun q hq => hv q (h hq))


theorem solution (src tgt : Set L0) : Cn src ⊆ Cn (Lift src tgt ∅) := by
  refine cn_mono' (fun p hp => ?_)
  exact Or.inr ⟨hp, fun h => h⟩
