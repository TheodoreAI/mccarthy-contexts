/-
  Lifting between contexts, and the failure of circumscription to determine one.

  McCarthy's `specializes` axiom is a default rule for transferring facts
  between contexts:

      specializes(c₁,c₂) ∧ ¬ab(p,c₁,c₂) ∧ ist(c₁,p) → ist(c₂,p)

  "what holds in a context still holds in a more specific one, unless it is
  abnormal for that transfer".  Note the shape: an abnormality predicate
  guarding a conditional, which is exactly the apparatus already built for
  contexts-as-theories.  This file generalises from one linear step to a
  transfer between two arbitrary contexts, which need not be stacked -- the
  Sherlock Holmes context and the US-legal-history context are siblings, not
  levels of one tower, and `specializes` relates contexts of that kind too.

  A transfer is modelled by a **blocking set** `A`: the assertions declared
  abnormal, hence not carried across.  Circumscribing `ab` means preferring a
  blocking set that is as small as possible.

  Three results.

  * `lift_transfers` -- with nothing blocked, everything the source asserts is
    available in the target.  Lifting does what it should when nothing is in
    the way.

  * `lift_defeasible` -- a target that contradicts the source forces something
    to be blocked, and the previously-available fact is then unavailable.  So
    the transfer is genuinely defeasible.

  * `lift_multiple_extensions` -- the payoff, and a negative result.  There are
    targets admitting **two incomparable minimal blocking sets**, so minimising
    abnormality does *not* pick out a unique lifted context.

  That last one completes an arc.  Over valuations, minimising change was
  degenerate in one direction: the minimum always existed and was always
  trivial.  Over theories with lifting it is degenerate in the opposite
  direction: minima exist, are non-trivial, and there is more than one.  Either
  way circumscription alone does not determine the context, which is the
  multiple-extensions problem of nonmonotonic logic appearing exactly where
  McCarthy's proposal needs it not to.
-/

import Definitions.Def_TranscendenceTowerContextTheories
import Mathlib.Data.Set.Basic

set_option autoImplicit false

open TranscendenceTower TranscendenceTower.ContextTheories

namespace TranscendenceTower.Lifting

/-! ## Lifting with a blocking set -/

/-- Lift `src` into `tgt`, carrying across every assertion of `src` except
those in the blocking set `A` (the ones declared abnormal for this transfer).

Assertions are lifted, not consequences: a context transfers what it *says*,
and the target draws its own conclusions.  Blocking a consequence set would be
ill-behaved anyway, since a set of consequences is closed under equivalence and
excluding `p` while retaining `¬¬p` blocks nothing. -/
def Lift (src tgt A : Set L0) : Set L0 := tgt ∪ (src \ A)

/-- A blocking set is **admissible** when the lifted context is satisfiable.
Declaring things abnormal is how a conflict gets resolved, so the question is
which declarations suffice. -/
def Admissible (src tgt A : Set L0) : Prop := ∃ v : Val, Models (Lift src tgt A) v

/-- A **minimal** blocking set: admissible, and no admissible blocking set is
strictly smaller.  This is the circumscription of `ab` for a single transfer --
block as little as possible. -/
def MinBlock (src tgt A : Set L0) : Prop :=
  Admissible src tgt A ∧ ∀ B : Set L0, Admissible src tgt B → B ⊆ A → A ⊆ B

theorem Cn_mono' {T T' : Set L0} (h : T ⊆ T') : Cn T ⊆ Cn T' :=
  fun _ hp v hv => hp v (fun q hq => hv q (h hq))

theorem subset_Cn' (T : Set L0) : T ⊆ Cn T := fun _ hp _ hv => hv _ hp

/-! ## 1. Unblocked lifting transfers everything -/

/-- With an empty blocking set the source's assertions are all present in the
lifted context, hence so are all their consequences. -/
theorem lift_transfers (src tgt : Set L0) :
    Cn src ⊆ Cn (Lift src tgt ∅) := by
  refine Cn_mono' (fun p hp => ?_)
  exact Or.inr ⟨hp, fun h => h⟩

/-! ## 2. Lifting is defeasible -/

/-- Atom `0`. -/
def pA : L0 := Form.atom 0
/-- Atom `1`. -/
def qA : L0 := Form.atom 1

/-- A source asserting `p`, and a target asserting `¬p`. -/
def srcP : Set L0 := {pA}
/-- The target contradicts the source outright. -/
def tgtNotP : Set L0 := {Form.neg pA}

/-- A valuation making `p` false. -/
def vNotP : Val := fun _ => false

/-- **Lifting is defeasible.**  When the target contradicts a source assertion,
the empty blocking set is inadmissible -- something *must* be declared abnormal
-- and once it is, the fact that would have transferred is no longer available
in the target. -/
theorem lift_defeasible :
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

/-! ## 3. Circumscription does not determine the lifted context -/

/-- A source asserting both `p` and `q`. -/
def srcPQ : Set L0 := {pA, qA}
/-- A target asserting that `p` and `q` are not both true.  It conflicts with
the source, but says nothing about *which* of them to give up. -/
def tgtNand : Set L0 := {Form.neg (Form.conj pA qA)}

/-- `p` true, `q` false. -/
def vP : Val := fun k => k == 0
/-- `q` true, `p` false. -/
def vQ : Val := fun k => k == 1

theorem admissible_block_p : Admissible srcPQ tgtNand {pA} := by
  refine ⟨vQ, ?_⟩
  rintro x (rfl | ⟨hx, hxA⟩)
  · rfl
  · rcases hx with rfl | rfl
    · exact absurd rfl hxA
    · rfl

theorem admissible_block_q : Admissible srcPQ tgtNand {qA} := by
  refine ⟨vP, ?_⟩
  rintro x (rfl | ⟨hx, hxA⟩)
  · rfl
  · rcases hx with rfl | rfl
    · rfl
    · exact absurd rfl hxA

/-- Blocking nothing is not admissible: the target forbids `p ∧ q` while the
source asserts both. -/
theorem not_admissible_empty : ¬ Admissible srcPQ tgtNand ∅ := by
  rintro ⟨v, hv⟩
  have hp : Form.eval v pA = true := hv pA (Or.inr ⟨Or.inl rfl, fun h => h⟩)
  have hq : Form.eval v qA = true := hv qA (Or.inr ⟨Or.inr rfl, fun h => h⟩)
  have hn : Form.eval v (Form.neg (Form.conj pA qA)) = true := hv _ (Or.inl rfl)
  rw [show Form.eval v (Form.neg (Form.conj pA qA))
        = !((Form.eval v pA) && (Form.eval v qA)) from rfl, hp, hq] at hn
  exact absurd hn (by decide)

/-- Each single-assertion block is minimal: its only proper subset is the empty
set, which is inadmissible. -/
theorem minblock_singleton {r : L0} (hadm : Admissible srcPQ tgtNand {r}) :
    MinBlock srcPQ tgtNand {r} := by
  refine ⟨hadm, fun B hB hsub => ?_⟩
  by_cases hr : r ∈ B
  · intro x hx
    rcases hx with rfl
    exact hr
  · -- the only proper subset of a singleton is empty, which is inadmissible
    exfalso
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
    exact not_admissible_empty hB

/-- **Circumscription does not determine the lifted context.**

There are two *incomparable minimal* blocking sets, so preferring to block as
little as possible leaves a genuine choice: give up `p`, or give up `q`.
Nothing in the abnormality-minimising semantics decides between them.

This is the multiple-extensions problem, arriving exactly where McCarthy's
`specializes` needs it not to.  Over valuations, minimisation was degenerate
because the minimum was always the trivial one; here it is degenerate because
there is more than one minimum.  Either way, minimisation alone does not
deliver a context. -/
theorem lift_multiple_extensions :
    ∃ A B : Set L0,
      MinBlock srcPQ tgtNand A ∧ MinBlock srcPQ tgtNand B
        ∧ ¬ (A ⊆ B) ∧ ¬ (B ⊆ A) := by
  refine ⟨{pA}, {qA}, minblock_singleton admissible_block_p,
          minblock_singleton admissible_block_q, ?_, ?_⟩
  · intro h
    have heq : pA = qA := h rfl
    injection heq with h0
    exact absurd h0 (by decide)
  · intro h
    have heq : qA = pA := h rfl
    injection heq with h0
    exact absurd h0 (by decide)

/-! ## Verification -/

section Verification

#print axioms lift_transfers
#print axioms lift_defeasible
#print axioms not_admissible_empty
#print axioms minblock_singleton
#print axioms lift_multiple_extensions

end Verification

end TranscendenceTower.Lifting
