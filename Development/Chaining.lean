/-
  Does lifting chain?

  `specializes` transfers a fact from one context to another unless it is
  abnormal for that transfer.  The obvious structural question is whether the
  relation composes: if a fact travels from c₁ to c₂, and from c₂ to c₃, does it
  arrive at c₃ by the same route it would have taken directly?

  It does not, and the reason is structural rather than incidental.  Lifting
  carries a context's *assertions* across, so a two-step route deposits the
  intermediate context's own commitments into the destination alongside those of
  the origin.  Those extra commitments can conflict with the destination even
  when the origin does not.

  The witness makes this concrete.  Take

      c₁ asserting p,        c₂ asserting q,       c₃ asserting ¬(p ∧ q).

  Note that c₁ and c₃ are perfectly compatible: p and ¬(p ∧ q) hold together.
  The conflict exists only along the route.

  * **Directly**, p transfers to c₃ and does so determinately: the empty
    blocking set is admissible, hence minimal, and p is a consequence of the
    result.

  * **Via c₂**, the transfer becomes indeterminate.  The intermediate step
    carries q along, so what arrives at c₃ is {p, q}, which does conflict.  Two
    incomparable minimal blocking sets appear -- give up p, or give up q -- and
    in the first of them p does not survive.

  So a transfer that succeeds determinately by the direct route can, by a longer
  route, become a choice in which the fact may be lost.  Lifting is
  **route-dependent**: `specializes` composes as a relation between contexts,
  but what it transfers does not compose along with it.

  This sharpens the multiple-extensions result rather than repeating it.  There,
  indeterminacy arose because the destination genuinely conflicted with the
  origin. Here the origin and destination are compatible, and the indeterminacy
  is manufactured entirely by passing through an intermediary.
-/

import Definitions.Def_TranscendenceTowerLiftConflicts
import Mathlib.Data.Set.Basic

set_option autoImplicit false

open TranscendenceTower TranscendenceTower.ContextTheories TranscendenceTower.Lifting

namespace TranscendenceTower.Chaining

/-- The intermediate context, asserting `q`.  It conflicts with neither the
origin nor the destination on its own. -/
def midQ : Set L0 := {qA}

theorem subset_Cn' (T : Set L0) : T ⊆ Cn T := fun _ hp _ hv => hv _ hp

/-! ## The direct route succeeds, determinately -/

/-- `p` and `¬(p ∧ q)` are jointly satisfiable, so nothing need be blocked. -/
theorem admissible_direct : Admissible srcP tgtNand ∅ := by
  refine ⟨vP, ?_⟩
  rintro x (rfl | ⟨rfl, _⟩)
  · rfl
  · rfl

/-- Nothing blocked is trivially minimal: no set is strictly below the empty
one. -/
theorem minblock_direct : MinBlock srcP tgtNand ∅ :=
  ⟨admissible_direct, fun _ _ _ => Set.empty_subset _⟩

/-- And `p` really does arrive. -/
theorem p_survives_direct : pA ∈ Cn (Lift srcP tgtNand ∅) :=
  subset_Cn' _ (Or.inr ⟨rfl, fun h => h⟩)

/-! ## The route through the intermediate context does not -/

/-- The first hop carries the intermediate context's own assertion along, so
what reaches `c₃` is `{p, q}` rather than `{p}`.  This single equation is the
whole mechanism. -/
theorem lift_through_mid : Lift srcP midQ ∅ = srcPQ := by
  ext x
  constructor
  · rintro (rfl | ⟨rfl, _⟩)
    · exact Or.inr rfl
    · exact Or.inl rfl
  · rintro (rfl | rfl)
    · exact Or.inr ⟨rfl, fun h => h⟩
    · exact Or.inl rfl

/-- Blocking nothing fails for the composite: `{p, q}` and `¬(p ∧ q)` clash. -/
theorem not_admissible_composite : ¬ Admissible srcPQ tgtNand ∅ := by
  rintro ⟨v, hv⟩
  have hp : Form.eval v pA = true := hv pA (Or.inr ⟨Or.inl rfl, fun h => h⟩)
  have hq : Form.eval v qA = true := hv qA (Or.inr ⟨Or.inr rfl, fun h => h⟩)
  have hn : Form.eval v (Form.neg (Form.conj pA qA)) = true := hv _ (Or.inl rfl)
  rw [show Form.eval v (Form.neg (Form.conj pA qA))
        = !((Form.eval v pA) && (Form.eval v qA)) from rfl, hp, hq] at hn
  exact absurd hn (by decide)

theorem admissible_drop_p : Admissible srcPQ tgtNand {pA} := by
  refine ⟨vQ, ?_⟩
  rintro x (rfl | ⟨hx, hxA⟩)
  · rfl
  · rcases hx with rfl | rfl
    · exact absurd rfl hxA
    · rfl

theorem admissible_drop_q : Admissible srcPQ tgtNand {qA} := by
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
    exact not_admissible_composite hB

/-- On the route through `c₂`, one of the two minimal resolutions loses `p`. -/
theorem p_lost_via_mid : pA ∉ Cn (Lift srcPQ tgtNand {pA}) := by
  intro h
  have hm : Models (Lift srcPQ tgtNand {pA}) vQ := by
    rintro x (rfl | ⟨hx, hxA⟩)
    · rfl
    · rcases hx with rfl | rfl
      · exact absurd rfl hxA
      · rfl
  exact absurd (h vQ hm) (by decide)

/-! ## Lifting is route-dependent -/

/-- **Lifting does not chain.**

By the direct route, `p` transfers from `c₁` to `c₃` and does so determinately:
the empty blocking set is minimal and `p` is a consequence of the result.

By the route through `c₂` it does not.  The first hop carries `c₂`'s own
assertion along, so `{p, q}` arrives at `c₃`; that conflicts, two incomparable
minimal blocking sets appear, and in one of them `p` is lost.

The origin and destination are compatible throughout -- `p` and `¬(p ∧ q)` hold
together.  The indeterminacy is created purely by passing through an
intermediary, which is why this is a statement about *routes* and not about the
endpoints. -/
theorem lifting_does_not_chain :
    (MinBlock srcP tgtNand ∅ ∧ pA ∈ Cn (Lift srcP tgtNand ∅))
      ∧ Lift srcP midQ ∅ = srcPQ
      ∧ MinBlock srcPQ tgtNand {pA}
      ∧ MinBlock srcPQ tgtNand {qA}
      ∧ pA ∉ Cn (Lift srcPQ tgtNand {pA}) :=
  ⟨⟨minblock_direct, p_survives_direct⟩,
   lift_through_mid,
   minblock_singleton' admissible_drop_p,
   minblock_singleton' admissible_drop_q,
   p_lost_via_mid⟩

/-! ## Verification -/

section Verification

#print axioms minblock_direct
#print axioms p_survives_direct
#print axioms lift_through_mid
#print axioms p_lost_via_mid
#print axioms lifting_does_not_chain

end Verification

end TranscendenceTower.Chaining
