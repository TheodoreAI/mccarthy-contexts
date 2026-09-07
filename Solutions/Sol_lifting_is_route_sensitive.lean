import Definitions.Def_TranscendenceTowerLiftConflicts

set_option autoImplicit false

open TranscendenceTower TranscendenceTower.ContextTheories TranscendenceTower.Lifting

theorem subset_Cn'' (T : Set L0) : T ⊆ Cn T := fun _ hp _ hv => hv _ hp

theorem admissible_direct' : Admissible srcP tgtNand ∅ := by
  refine ⟨vP, ?_⟩
  rintro x (rfl | ⟨rfl, _⟩)
  · rfl
  · rfl

theorem minblock_direct_unique' {A : Set L0}
    (hA : MinBlock srcP tgtNand A) : A = ∅ := by
  apply Set.Subset.antisymm
  · exact hA.2 ∅ admissible_direct' (Set.empty_subset A)
  · exact Set.empty_subset A

theorem p_survives_direct' : pA ∈ Cn (Lift srcP tgtNand ∅) :=
  subset_Cn'' _ (Or.inr ⟨rfl, fun h => h⟩)

theorem p_survives_every_direct' (A : Set L0)
    (hA : MinBlock srcP tgtNand A) :
    pA ∈ Cn (Lift srcP tgtNand A) := by
  rw [minblock_direct_unique' hA]
  exact p_survives_direct'

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

theorem minblock_singleton'' {r : L0}
    (hadm : Admissible srcPQ tgtNand {r}) :
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

theorem p_survives_via_mid' : pA ∈ Cn (Lift srcPQ tgtNand {qA}) := by
  apply subset_Cn'' _
  refine Or.inr ⟨Or.inl rfl, ?_⟩
  intro hpq
  have heq : pA = qA := hpq
  injection heq with h0
  exact absurd h0 (by decide)

theorem solution :
    (∀ A : Set L0, MinBlock srcP tgtNand A →
      pA ∈ Cn (Lift srcP tgtNand A))
      ∧ Lift srcP {qA} ∅ = srcPQ
      ∧ (∃ A : Set L0, MinBlock srcPQ tgtNand A
          ∧ pA ∉ Cn (Lift srcPQ tgtNand A))
      ∧ (∃ A : Set L0, MinBlock srcPQ tgtNand A
          ∧ pA ∈ Cn (Lift srcPQ tgtNand A)) :=
  ⟨p_survives_every_direct',
   lift_through_mid',
   ⟨{pA}, minblock_singleton'' admissible_drop_p', p_lost_via_mid'⟩,
   ⟨{qA}, minblock_singleton'' admissible_drop_q', p_survives_via_mid'⟩⟩
