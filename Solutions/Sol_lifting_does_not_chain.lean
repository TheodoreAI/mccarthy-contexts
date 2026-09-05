import Definitions.Def_TranscendenceTowerLiftConflicts

set_option autoImplicit false

open TranscendenceTower TranscendenceTower.ContextTheories TranscendenceTower.Lifting

theorem subset_Cn'' (T : Set L0) : T ⊆ Cn T := fun _ hp _ hv => hv _ hp

theorem admissible_direct' : Admissible srcP tgtNand ∅ := by
  refine ⟨vP, ?_⟩
  rintro x (rfl | ⟨rfl, _⟩)
  · rfl
  · rfl

theorem minblock_direct' : MinBlock srcP tgtNand ∅ :=
  ⟨admissible_direct', fun _ _ _ => Set.empty_subset _⟩

theorem p_survives_direct' : pA ∈ Cn (Lift srcP tgtNand ∅) :=
  subset_Cn'' _ (Or.inr ⟨rfl, fun h => h⟩)

/-- The first hop carries the intermediate context's own assertion along. -/
theorem lift_through_mid' : Lift srcP {qA} ∅ = srcPQ := by
  ext x
  constructor
  · rintro (rfl | ⟨rfl, _⟩)
    · exact Or.inr rfl
    · exact Or.inl rfl
  · rintro (rfl | rfl)
    · exact Or.inr ⟨rfl, fun h => h⟩
    · exact Or.inl rfl

theorem not_admissible_composite' : ¬ Admissible srcPQ tgtNand ∅ := by
  rintro ⟨v, hv⟩
  have hp : Form.eval v pA = true := hv pA (Or.inr ⟨Or.inl rfl, fun h => h⟩)
  have hq : Form.eval v qA = true := hv qA (Or.inr ⟨Or.inr rfl, fun h => h⟩)
  have hn : Form.eval v (Form.neg (Form.conj pA qA)) = true := hv _ (Or.inl rfl)
  rw [show Form.eval v (Form.neg (Form.conj pA qA))
        = !((Form.eval v pA) && (Form.eval v qA)) from rfl, hp, hq] at hn
  exact absurd hn (by decide)

theorem admissible_drop_p' : Admissible srcPQ tgtNand {pA} := by
  refine ⟨vQ, ?_⟩
  rintro x (rfl | ⟨hx, hxA⟩)
  · rfl
  · rcases hx with rfl | rfl
    · exact absurd rfl hxA
    · rfl

theorem admissible_drop_q' : Admissible srcPQ tgtNand {qA} := by
  refine ⟨vP, ?_⟩
  rintro x (rfl | ⟨hx, hxA⟩)
  · rfl
  · rcases hx with rfl | rfl
    · rfl
    · exact absurd rfl hxA

theorem minblock_singleton'' {r : L0} (hadm : Admissible srcPQ tgtNand {r}) :
    MinBlock srcPQ tgtNand {r} := by
  refine ⟨hadm, fun B hB hsub => ?_⟩
  by_cases hr : r ∈ B
  · intro x hx
    rcases hx with rfl
    exact hr
  · exfalso
    have hBempty : B = ∅ := by
      ext y
      constructor
      · intro hy
        have hyr : y = r := hsub hy
        subst hyr
        exact absurd hy hr
      · intro hy
        exact hy.elim
    rw [hBempty] at hB
    exact not_admissible_composite' hB

theorem p_lost_via_mid' : pA ∉ Cn (Lift srcPQ tgtNand {pA}) := by
  intro h
  have hm : Models (Lift srcPQ tgtNand {pA}) vQ := by
    rintro x (rfl | ⟨hx, hxA⟩)
    · rfl
    · rcases hx with rfl | rfl
      · exact absurd rfl hxA
      · rfl
  exact absurd (h vQ hm) (by decide)

theorem solution :
    (MinBlock srcP tgtNand ∅ ∧ pA ∈ Cn (Lift srcP tgtNand ∅))
      ∧ Lift srcP {qA} ∅ = srcPQ
      ∧ MinBlock srcPQ tgtNand {pA}
      ∧ MinBlock srcPQ tgtNand {qA}
      ∧ pA ∉ Cn (Lift srcPQ tgtNand {pA}) :=
  ⟨⟨minblock_direct', p_survives_direct'⟩,
   lift_through_mid',
   minblock_singleton'' admissible_drop_p',
   minblock_singleton'' admissible_drop_q',
   p_lost_via_mid'⟩
