/-
  Uniformity: the monotone dichotomy.

  A monotone, proposition-uniform lifting schema is conservative over a
  context-free base theory.  Novelty and uniformity are incompatible already
  in the monotone case, where uniqueness of the extension is automatic.

  Two departures from the paper's proof, both simplifications.

  * The frame plays no role.  The paper observes this in a remark; here it is
    structural, since nothing below mentions an `out` map.  Contexts are an
    arbitrary index type.

  * The argument is semantic rather than proof-theoretic.  The paper extracts
    a finite derivation and applies substitution to it, which needs a proof
    calculus and compactness.  Composing valuations instead gives the
    substitution lemma directly, and the theorem follows with neither.

  For monotone schemas the extension is `Cn (T ∪ Γ)` with `Γ` the set of
  consequents, so the Reiter fixed point does not appear either.
-/

import Mathlib.Data.Set.Basic
import Mathlib.Tactic

set_option autoImplicit false

namespace TranscendenceTower.Uniformity

/-! ## The context language -/

/-- Propositional formulas over atoms `A`, with a modality `ist c` for each
context `c : C`.  Following the paper, `ist c φ` is an additional atom: the
language is closed under the Boolean connectives and nothing constrains the
modality. -/
inductive CForm (A : Type) (C : Type) : Type where
  | atom : A → CForm A C
  | fls : CForm A C
  | impl : CForm A C → CForm A C → CForm A C
  | ist : C → CForm A C → CForm A C
  deriving DecidableEq

namespace CForm

variable {A C : Type}

/-- Truth. -/
def tru : CForm A C := .impl .fls .fls

end CForm

/-- A valuation assigns a truth value to every atom and to every
`ist`-formula; the connectives are then interpreted classically. -/
structure CVal (A C : Type) where
  /-- Truth values of the atoms. -/
  atom : A → Bool
  /-- Truth values of the modal atoms. -/
  ist : C → CForm A C → Bool

variable {A C : Type}

/-- Classical evaluation. -/
def eval (v : CVal A C) : CForm A C → Bool
  | .atom a => v.atom a
  | .fls => false
  | .impl p q => !(eval v p) || eval v q
  | .ist c p => v.ist c p

@[simp] theorem eval_tru (v : CVal A C) : eval v CForm.tru = true := rfl

/-- `v` satisfies every member of `T`. -/
def Models (T : Set (CForm A C)) (v : CVal A C) : Prop :=
  ∀ p ∈ T, eval v p = true

/-- Semantic consequence. -/
def Cn (T : Set (CForm A C)) : Set (CForm A C) :=
  {p | ∀ v, Models T v → eval v p = true}

/-- A theory is consistent when it has a model. -/
def Consistent (T : Set (CForm A C)) : Prop := ∃ v, Models T v

theorem subset_Cn (T : Set (CForm A C)) : T ⊆ Cn T :=
  fun _ hp v hv => hv _ hp

/-! ## The base language -/

/-- The base language: no context machinery.  This is the paper's `L` inside
`L⁺`. -/
def IsBase : CForm A C → Prop
  | .atom _ => True
  | .fls => True
  | .impl p q => IsBase p ∧ IsBase q
  | .ist _ _ => False

/-! ## Substitution

Substitutions act on atoms and are extended homomorphically, acting inside
the scope of `ist`.  This is the paper's proposition-uniformity apparatus. -/

/-- Homomorphic extension of an atom substitution. -/
def subst (s : A → CForm A C) : CForm A C → CForm A C
  | .atom a => s a
  | .fls => .fls
  | .impl p q => .impl (subst s p) (subst s q)
  | .ist c p => .ist c (subst s p)

/-- The valuation that a substitution pulls back: read an atom through `s`,
and read a modal atom through its substituted form.  This is what makes the
substitution lemma hold without a proof calculus. -/
def pullback (v : CVal A C) (s : A → CForm A C) : CVal A C where
  atom a := eval v (s a)
  ist c p := v.ist c (subst s p)

/-- **The substitution lemma.**  Evaluating a substituted formula is
evaluating the original against the pulled-back valuation. -/
theorem eval_subst (v : CVal A C) (s : A → CForm A C) (p : CForm A C) :
    eval v (subst s p) = eval (pullback v s) p := by
  induction p with
  | atom a => rfl
  | fls => rfl
  | impl p q ihp ihq => simp [eval, subst, ihp, ihq]
  | ist c p _ => rfl

/-- Semantic consequence is preserved by substitution. -/
theorem subst_Cn {T : Set (CForm A C)} {p : CForm A C} (s : A → CForm A C)
    (h : p ∈ Cn T) : subst s p ∈ Cn (subst s '' T) := by
  intro v hv
  rw [eval_subst]
  refine h _ fun q hq => ?_
  have := hv (subst s q) ⟨q, hq, rfl⟩
  rwa [eval_subst] at this

/-! ## Freezing a model into a substitution -/

/-- The substitution that replaces each atom by its truth value in `M`. -/
def boolSubst (M : CVal A C) : A → CForm A C :=
  fun a => bif M.atom a then CForm.tru else CForm.fls

/-- On the base language, the frozen substitution evaluates to `M`
regardless of the ambient valuation: every atom has become a constant. -/
theorem eval_boolSubst (M v : CVal A C) :
    ∀ p : CForm A C, IsBase p → eval v (subst (boolSubst M) p) = eval M p := by
  intro p
  induction p with
  | atom a =>
    intro _
    cases h : M.atom a <;> simp [subst, boolSubst, h, eval]
  | fls => intro _; rfl
  | impl p q ihp ihq =>
    intro hb
    simp [subst, eval, ihp hb.1, ihq hb.2]
  | ist c p _ => intro hb; exact hb.elim

/-! ## The monotone dichotomy -/

/-- A set of consequents is **proposition-uniform** when it is closed under
substitution: a rule about lifting is a rule about lifting *anything*. -/
def PropUniform (Γ : Set (CForm A C)) : Prop :=
  ∀ (s : A → CForm A C), ∀ p ∈ Γ, subst s p ∈ Γ

/-- **Monotone dichotomy.**  Let the base theory `T` be context-free and let
the schema's consequents `Γ` be proposition-uniform.  Then either the
extension `Cn (T ∪ Γ)` is inconsistent, or it proves no new base sentence.

Uniformity and novelty are incompatible: a rule indifferent to which
proposition it lifts cannot deliver a particular new fact, because under
substitution it would have to deliver every instance of that fact, and those
are jointly unsatisfiable. -/
theorem monotone_dichotomy {T Γ : Set (CForm A C)}
    (hT : ∀ p ∈ T, IsBase p) (hU : PropUniform Γ)
    (hcon : Consistent (T ∪ Γ)) :
    ∀ φ : CForm A C, IsBase φ → φ ∈ Cn (T ∪ Γ) → φ ∈ Cn T := by
  intro φ hφ hmem
  by_contra hnot
  simp only [Cn, Set.mem_setOf_eq] at hnot
  push Not at hnot
  obtain ⟨M, hMT, hMφ⟩ := hnot
  obtain ⟨v, hv⟩ := hcon
  -- Freeze `M` into a substitution and pull `v` back along it.
  have hmodels : Models (T ∪ Γ) (pullback v (boolSubst M)) := by
    intro q hq
    rw [← eval_subst]
    rcases hq with hq | hq
    · rw [eval_boolSubst M v q (hT q hq)]
      exact hMT q hq
    · exact hv _ (Or.inr (hU (boolSubst M) q hq))
  have h1 : eval (pullback v (boolSubst M)) φ = true := hmem _ hmodels
  rw [← eval_subst, eval_boolSubst M v φ hφ] at h1
  exact hMφ h1

/-- Conservativity, in the paper's formulation: the extension meets the base
language in exactly the base consequences of `T`. -/
theorem conservative {T Γ : Set (CForm A C)}
    (hT : ∀ p ∈ T, IsBase p) (hU : PropUniform Γ)
    (hcon : Consistent (T ∪ Γ)) :
    {φ : CForm A C | IsBase φ ∧ φ ∈ Cn (T ∪ Γ)}
      = {φ : CForm A C | IsBase φ ∧ φ ∈ Cn T} := by
  ext φ
  constructor
  · rintro ⟨hφ, hmem⟩
    exact ⟨hφ, monotone_dichotomy hT hU hcon φ hφ hmem⟩
  · rintro ⟨hφ, hmem⟩
    refine ⟨hφ, fun v hv => hmem v fun q hq => hv q (Or.inl hq)⟩

/-! ## Non-vacuity

The hypotheses are satisfiable by the intended example.  The copy schema —
every context reports the level below faithfully — is proposition-uniform and
consistent, so the theorem says something about it rather than about an empty
class of schemas. -/

/-- The consequents of the copy schema: `ist c p → p`, for every context and
every formula. -/
def copySchema (A C : Type) : Set (CForm A C) :=
  {q | ∃ (c : C) (p : CForm A C), q = CForm.impl (CForm.ist c p) p}

theorem copySchema_propUniform : PropUniform (copySchema A C) := by
  rintro s q ⟨c, p, rfl⟩
  exact ⟨c, subst s p, rfl⟩

/-- The canonical evaluation in which `ist c p` says exactly what `p` says. -/
def canon (atomv : A → Bool) : CForm A C → Bool
  | .atom a => atomv a
  | .fls => false
  | .impl p q => !(canon atomv p) || canon atomv q
  | .ist _ p => canon atomv p

/-- The valuation built from the canonical evaluation. -/
def canonVal (atomv : A → Bool) : CVal A C where
  atom := atomv
  ist := fun _ p => canon atomv p

theorem eval_canonVal (atomv : A → Bool) (p : CForm A C) :
    eval (canonVal atomv) p = canon atomv p := by
  induction p with
  | atom a => rfl
  | fls => rfl
  | impl p q ihp ihq => simp [eval, canon, ihp, ihq]
  | ist c p _ => rfl

/-- The copy schema is consistent: the canonical valuation models it. -/
theorem copySchema_consistent (atomv : A → Bool) :
    Models (copySchema A C) (canonVal atomv) := by
  rintro q ⟨c, p, rfl⟩
  have hist : eval (canonVal atomv) (CForm.ist c p) = canon atomv p := rfl
  show (!(eval (canonVal atomv) (CForm.ist c p)) || eval (canonVal atomv) p) = true
  rw [hist, eval_canonVal]
  cases h : canon atomv p <;> rfl

/-- So the dichotomy applies non-trivially: with the tautological base and the
copy schema, the hypotheses hold and the conclusion is that nothing new is
derivable at the base. -/
theorem copySchema_conservative (atomv : A → Bool) :
    ∀ φ : CForm A C, IsBase φ → φ ∈ Cn ((∅ : Set (CForm A C)) ∪ copySchema A C) →
      φ ∈ Cn (∅ : Set (CForm A C)) := by
  refine monotone_dichotomy (fun p hp => hp.elim) copySchema_propUniform ?_
  refine ⟨canonVal atomv, fun q hq => ?_⟩
  rcases hq with hq | hq
  · exact hq.elim
  · exact copySchema_consistent atomv q hq

section Verification

#print axioms eval_subst
#print axioms monotone_dichotomy
#print axioms conservative
#print axioms copySchema_conservative

end Verification

end TranscendenceTower.Uniformity
