/-
  Contexts as theories, and a nonmonotonicity theorem.

  The preceding development models a context as a *valuation* and shows that
  relaxing an assumption leaves the transcending context underdetermined in a
  very rigid way: the change set parametrises the relaxed models exactly, the
  minimal-change reading always returns the unrelaxed tower, and specifying the
  change set fixes the context uniquely.  The injectivity there rests on truth
  values being Boolean -- knowing *where* a context departs from the one below
  determines *what* it says there, because only one alternative exists.

  That rigidity is what blocks a preference-based semantics, so the next step
  changes the setting rather than the preference order.  Here a context is a
  *theory* `T` (a set of sentences), and "true in the context" means derivable
  from it.  Relaxing an assumption now removes a sentence from `T`, which alters
  a whole consequence set rather than flipping a single bit.

  Classically that direction is monotone (`Cn_mono`): a smaller theory proves
  less, so relaxation could only ever lose conclusions.  The interesting
  behaviour needs the nonmonotonic apparatus McCarthy invented for exactly this
  purpose.  We add an abnormality predicate and define consequence over the
  models that minimise abnormality (`CnCirc`), which is circumscription.

  The main result, `circ_nonmonotone`, exhibits theories `T' ⊆ T` and a sentence
  `φ` with

      φ ∈ CnCirc T'   but   φ ∉ CnCirc T,

  so enlarging the theory *destroys* a conclusion -- equivalently, relaxing an
  assumption *creates* one.  This is McCarthy's dropped-assumption phenomenon
  made formal, and it is exactly what the valuation-based setting could not
  produce.

  Reuses the published propositional core rather than redefining it.
-/

import Definitions.Def_TranscendenceTowerCore
import Mathlib.Data.Set.Basic

set_option autoImplicit false

open TranscendenceTower

namespace TranscendenceTower.Theories

/-- Sentences of the base language. -/
abbrev L0 : Type := Form Base

/-- A valuation of the base language. -/
abbrev Val : Type := Base → Bool

/-! ## Contexts as theories, and classical consequence -/

/-- `v` is a model of the theory `T`. -/
def Models (T : Set L0) (v : Val) : Prop := ∀ p ∈ T, Form.eval v p = true

/-- Classical consequence: what holds in every model of `T`.  This is "true in
the context `T`", the reading of `ist` appropriate to contexts-as-theories. -/
def Cn (T : Set L0) : Set L0 := {p | ∀ v : Val, Models T v → Form.eval v p = true}

/-- A theory entails its own axioms. -/
theorem subset_Cn (T : Set L0) : T ⊆ Cn T := fun _ hp _ hv => hv _ hp

/-- **Classical consequence is monotone.**  Removing an assumption can only lose
conclusions, never gain them.  So in the classical setting relaxation is
uninteresting in exactly the way the valuation-based development found it to be:
nothing new can ever follow from assuming less. -/
theorem Cn_mono {T T' : Set L0} (h : T ⊆ T') : Cn T ⊆ Cn T' :=
  fun _ hp v hv => hp v (fun q hq => hv q (h hq))

/-! ## Circumscription -/

/-- The abnormal atoms made true by `v`, relative to a designated set `ab` of
abnormality atoms. -/
def AbSet (ab : Set Base) (v : Val) : Set Base := {k | k ∈ ab ∧ v k = true}

/-- `v` is a model of `T` minimising abnormality: no model of `T` is strictly
more normal.  This is McCarthy's circumscription, stated as minimality of the
extension of the abnormality predicate. -/
def MinModel (ab : Set Base) (T : Set L0) (v : Val) : Prop :=
  Models T v ∧ ∀ w : Val, Models T w → AbSet ab w ⊆ AbSet ab v → AbSet ab v ⊆ AbSet ab w

/-- Circumscriptive consequence: what holds in every minimal model. -/
def CnCirc (ab : Set Base) (T : Set L0) : Set L0 :=
  {p | ∀ v : Val, MinModel ab T v → Form.eval v p = true}

/-- Circumscription is at least as strong as classical consequence, since every
minimal model is a model. -/
theorem Cn_subset_CnCirc (ab : Set Base) (T : Set L0) : Cn T ⊆ CnCirc ab T :=
  fun _ hp v hv => hp v hv.1

/-! ## A concrete context

`bird`, `flies`, and an abnormality atom.  The default rule says a bird flies
unless abnormal.  The small theory asserts only that we have a bird; the large
theory additionally asserts abnormality. -/

/-- Atom `0`: the subject is a bird. -/
def bird : L0 := Form.atom 0
/-- Atom `1`: the subject flies. -/
def flies : L0 := Form.atom 1
/-- Atom `2`: the subject is abnormal.  This is the only abnormality atom. -/
def abn : L0 := Form.atom 2

/-- The default rule: a bird flies unless abnormal. -/
def defaultRule : L0 := Form.impl (Form.conj bird (Form.neg abn)) flies

/-- The designated abnormality atoms. -/
def abAtoms : Set Base := {2}

/-- The smaller context: a bird, and the default. -/
def Tsmall : Set L0 := {bird, defaultRule}

/-- The larger context: additionally, the subject is abnormal. -/
def Tbig : Set L0 := {bird, defaultRule, abn}

theorem Tsmall_subset_Tbig : Tsmall ⊆ Tbig := by
  intro p hp
  rcases hp with h | h
  · exact Or.inl h
  · exact Or.inr (Or.inl h)

/-- The normal witness: a bird that flies and is not abnormal. -/
def vNormal : Val := fun k => k == 0 || k == 1

/-- The abnormal witness: a bird that is abnormal and does not fly. -/
def vAbnormal : Val := fun k => k == 0 || k == 2

theorem models_Tsmall_vNormal : Models Tsmall vNormal := by
  rintro p (rfl | rfl) <;> rfl

theorem models_Tbig_vAbnormal : Models Tbig vAbnormal := by
  rintro p (rfl | rfl | rfl) <;> rfl

theorem abset_vNormal : AbSet abAtoms vNormal = ∅ := by
  ext k
  constructor
  · rintro ⟨hk, hv⟩
    rw [show k = 2 from hk] at hv
    exact absurd hv (by decide)
  · intro h
    exact absurd h (by simp)

/-- Every model of the larger theory is abnormal, since it asserts abnormality
outright. -/
theorem two_mem_abset_of_models_Tbig {w : Val} (hw : Models Tbig w) :
    (2 : Base) ∈ AbSet abAtoms w :=
  ⟨rfl, hw abn (Or.inr (Or.inr rfl))⟩

/-! ## The normal context concludes that the bird flies -/

/-- In the smaller context, minimality forces normality. -/
theorem minmodel_Tsmall_not_abnormal {v : Val} (h : MinModel abAtoms Tsmall v) :
    v 2 = false := by
  by_contra hv
  have hv2 : v 2 = true := by
    cases hvv : v 2 with
    | false => exact absurd hvv hv
    | true => rfl
  have hmem : (2 : Base) ∈ AbSet abAtoms v := ⟨rfl, hv2⟩
  have hsub : AbSet abAtoms vNormal ⊆ AbSet abAtoms v := by
    rw [abset_vNormal]
    exact Set.empty_subset _
  have hv' := h.2 vNormal models_Tsmall_vNormal hsub
  rw [abset_vNormal] at hv'
  exact absurd (hv' hmem) (by simp)

/-- **Non-vacuity**: the smaller context does have a minimal model, so the
conclusion below is not vacuously true. -/
theorem minmodel_Tsmall_vNormal : MinModel abAtoms Tsmall vNormal := by
  refine ⟨models_Tsmall_vNormal, fun w _ _ => ?_⟩
  rw [abset_vNormal]
  exact Set.empty_subset _

/-- In the smaller context, every minimal model has the bird flying. -/
theorem flies_mem_CnCirc_Tsmall : flies ∈ CnCirc abAtoms Tsmall := by
  intro v hv
  have hab : v 2 = false := minmodel_Tsmall_not_abnormal hv
  have hbird : Form.eval v bird = true := hv.1 bird (Or.inl rfl)
  have hdef : Form.eval v defaultRule = true := hv.1 defaultRule (Or.inr rfl)
  -- `defaultRule` evaluates to `!(v 0 && !(v 2)) || v 1`
  show v 1 = true
  simp only [defaultRule, bird, flies, abn, Form.eval] at hdef
  simp only [bird, Form.eval] at hbird
  rw [hbird, hab] at hdef
  simpa using hdef

/-! ## The abnormal context does not -/

/-- `vAbnormal` is a minimal model of the larger theory: every model of it is
abnormal, so no model is more normal. -/
theorem minmodel_Tbig_vAbnormal : MinModel abAtoms Tbig vAbnormal := by
  refine ⟨models_Tbig_vAbnormal, fun w hw _ => ?_⟩
  rintro k ⟨hk, _⟩
  rw [show k = 2 from hk]
  exact two_mem_abset_of_models_Tbig hw

theorem flies_not_mem_CnCirc_Tbig : flies ∉ CnCirc abAtoms Tbig := by
  intro h
  have := h vAbnormal minmodel_Tbig_vAbnormal
  exact absurd this (by decide)

/-- **The conclusion is genuinely default-driven.**  `flies` does *not* follow
classically from the smaller context: the abnormal valuation models `Tsmall`
without flying, since the default rule's antecedent fails there.

Without this the nonmonotonicity result would be much weaker -- one could object
that `flies` was already a classical consequence and that circumscription merely
inherited it. -/
theorem flies_not_mem_Cn_Tsmall : flies ∉ Cn Tsmall := by
  intro h
  have hm : Models Tsmall vAbnormal := by rintro p (rfl | rfl) <;> rfl
  exact absurd (h vAbnormal hm) (by decide)

/-! ## Nonmonotonicity -/

/-- **Circumscriptive consequence is nonmonotone.**

There are theories `T' ⊆ T` and a sentence `φ` with `φ ∈ CnCirc T'` but
`φ ∉ CnCirc T`.  Enlarging the context destroys a conclusion; equivalently,
*relaxing* an assumption creates one.

This is what the valuation-based setting could not produce.  There, relaxation
left a rigidly parametrised family of contexts whose minimal element always
changed nothing.  Here, dropping the abnormality assumption changes which models
are minimal, and hence what follows -- so relaxation does real inferential work.

Note that the classical consequence operator on the same theories is monotone
(`Cn_mono`), so the phenomenon comes entirely from the abnormality-minimising
semantics, not from the change of setting alone. -/
theorem circ_nonmonotone :
    ∃ (ab : Set Base) (T T' : Set L0) (φ : L0),
      T' ⊆ T ∧ φ ∈ CnCirc ab T' ∧ φ ∉ CnCirc ab T :=
  ⟨abAtoms, Tbig, Tsmall, flies,
   Tsmall_subset_Tbig, flies_mem_CnCirc_Tsmall, flies_not_mem_CnCirc_Tbig⟩

/-- The whole phenomenon in one statement, on a single sentence `flies` and a
single pair of contexts.

* Classically, the smaller context leaves `flies` open.
* Circumscribing abnormality, the smaller context concludes `flies`.
* Adding the abnormality assumption *withdraws* that conclusion.

So the default reasoning is doing genuine inferential work, and it is defeasible
in exactly the way McCarthy's dropped-assumption example requires. -/
theorem default_reasoning_works :
    flies ∉ Cn Tsmall
      ∧ flies ∈ CnCirc abAtoms Tsmall
      ∧ flies ∉ CnCirc abAtoms Tbig :=
  ⟨flies_not_mem_Cn_Tsmall, flies_mem_CnCirc_Tsmall, flies_not_mem_CnCirc_Tbig⟩

/-! ## Verification -/

section Verification

#print axioms flies_not_mem_Cn_Tsmall
#print axioms default_reasoning_works
#print axioms Cn_mono
#print axioms Cn_subset_CnCirc
#print axioms minmodel_Tsmall_vNormal
#print axioms flies_mem_CnCirc_Tsmall
#print axioms minmodel_Tbig_vAbnormal
#print axioms flies_not_mem_CnCirc_Tbig
#print axioms circ_nonmonotone

end Verification

end TranscendenceTower.Theories
