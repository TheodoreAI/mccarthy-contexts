import Definitions.Def_TranscendenceTowerLiftConflicts

set_option autoImplicit false

open TranscendenceTower TranscendenceTower.ContextTheories TranscendenceTower.Lifting

theorem not_admissible_empty' : ¬ Admissible srcPQ tgtNand ∅ := by
  rintro ⟨v, hv⟩
  have hp : Form.eval v pA = true := hv pA (Or.inr ⟨Or.inl rfl, fun h => h⟩)
  have hq : Form.eval v qA = true := hv qA (Or.inr ⟨Or.inr rfl, fun h => h⟩)
  have hn : Form.eval v (Form.neg (Form.conj pA qA)) = true := hv _ (Or.inl rfl)
  rw [show Form.eval v (Form.neg (Form.conj pA qA))
        = !((Form.eval v pA) && (Form.eval v qA)) from rfl, hp, hq] at hn
  exact absurd hn (by decide)

theorem admissible_block_p' : Admissible srcPQ tgtNand {pA} := by
  refine ⟨vQ, ?_⟩
  rintro x (rfl | ⟨hx, hxA⟩)
  · rfl
  · rcases hx with rfl | rfl
    · exact absurd rfl hxA
    · rfl

theorem admissible_block_q' : Admissible srcPQ tgtNand {qA} := by
  refine ⟨vP, ?_⟩
  rintro x (rfl | ⟨hx, hxA⟩)
  · rfl
  · rcases hx with rfl | rfl
    · rfl
    · exact absurd rfl hxA

theorem minblock_singleton' {r : L0} (hadm : Admissible srcPQ tgtNand {r}) :
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
    exact not_admissible_empty' hB


theorem solution :
    ¬ Admissible srcP tgtNotP ∅
      ∧ Admissible srcP tgtNotP {pA}
      ∧ pA ∉ Cn (Lift srcP tgtNotP {pA}) := by
  refine ⟨?_, ?_, ?_⟩
  · rintro ⟨v, hv⟩
    have h1 : Form.eval v pA = true := hv pA (Or.inr ⟨rfl, fun h => h⟩)
    have h2 : Form.eval v (Form.neg pA) = true := hv _ (Or.inl rfl)
    rw [show Form.eval v (Form.neg pA) = !(Form.eval v pA) from rfl, h1] at h2
    exact absurd h2 (by decide)
  · refine ⟨vNotP, ?_⟩
    rintro x (rfl | ⟨rfl, hx⟩)
    · rfl
    · exact absurd rfl hx
  · intro h
    have hm : Models (Lift srcP tgtNotP {pA}) vNotP := by
      rintro x (rfl | ⟨rfl, hx⟩)
      · rfl
      · exact absurd rfl hx
    exact absurd (h vNotP hm) (by decide)
