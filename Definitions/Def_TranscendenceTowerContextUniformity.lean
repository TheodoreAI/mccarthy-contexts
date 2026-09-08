/-
Definitions for the uniformity results: the context language with signed atoms,
valuations and semantic consequence, default rules and Reiter extensions,
logical automorphisms of the context language, and the two families of
automorphism the theorems use — the shift along a frame map and the atom
automorphisms of `Aut(L)`.

Definitions only, together with the proof obligations that constructing them
requires: an `Equiv` cannot be written down without its two inverse laws, and
a logical automorphism cannot be written down without the lemma relating its
action on formulas to its action on valuations.  Every substantive claim about
these objects is proved in the theorems that import this bundle.

Atoms carry a sign.  `lit a false` is the atom `a` and `lit a true` is its
negation, and `neg` flips that sign rather than forming `p → ⊥`.  The reason is
that an atom automorphism must be a bijection of *formulas*: with unsigned
atoms, applying a sign flip twice to `a` yields `¬¬a`, a different formula, so
the group acts only on the Lindenbaum algebra and the preimage of a schema is
not the schema.
-/

import Mathlib.Data.Set.Basic
import Mathlib.Tactic

set_option autoImplicit false

namespace TranscendenceTower.UniformityPlatform

/-! ## The context language -/

/-- Formulas over signed atoms `A`, with a modality `ist c` for each context
`c : C`.  `ist c φ` is an additional atom: the language is closed under the
Boolean connectives and nothing constrains the modality. -/
inductive CForm (A : Type) (C : Type) : Type where
  /-- A signed atom: `lit a false` is `a`, and `lit a true` is `¬a`. -/
  | lit : A → Bool → CForm A C
  /-- Falsity. -/
  | fls : CForm A C
  /-- Material implication. -/
  | impl : CForm A C → CForm A C → CForm A C
  /-- `ist c p`: `p` holds in context `c`. -/
  | ist : C → CForm A C → CForm A C
  deriving DecidableEq

namespace CForm

variable {A C : Type}

/-- The positive literal on `a`. -/
def atom (a : A) : CForm A C := .lit a false

/-- Truth. -/
def tru : CForm A C := .impl .fls .fls

end CForm

variable {A C : Type}

/-- Negation.  On a literal it flips the sign, so it is an involution there;
elsewhere it is the usual `p → ⊥`. -/
def neg : CForm A C → CForm A C
  | .lit a b => .lit a (!b)
  | .fls => CForm.impl .fls .fls
  | .impl p q => CForm.impl (.impl p q) .fls
  | .ist c p => CForm.impl (.ist c p) .fls

@[simp] theorem neg_lit (a : A) (b : Bool) :
    neg (CForm.lit a b : CForm A C) = CForm.lit a (!b) := rfl

/-- A valuation assigns a truth value to every atom and to every
`ist`-formula; the connectives are then interpreted classically. -/
structure CVal (A C : Type) where
  /-- Truth values of the atoms. -/
  atom : A → Bool
  /-- Truth values of the modal atoms. -/
  ist : C → CForm A C → Bool

/-- Classical evaluation.  A literal is read off its sign. -/
def eval (v : CVal A C) : CForm A C → Bool
  | .lit a b => xor b (v.atom a)
  | .fls => false
  | .impl p q => !(eval v p) || eval v q
  | .ist c p => v.ist c p

@[simp] theorem eval_tru (v : CVal A C) : eval v CForm.tru = true := rfl

@[simp] theorem eval_lit (v : CVal A C) (a : A) (b : Bool) :
    eval v (CForm.lit a b) = xor b (v.atom a) := rfl

@[simp] theorem eval_neg (v : CVal A C) (p : CForm A C) :
    eval v (neg p) = !(eval v p) := by
  cases p with
  | lit a b => cases b <;> simp [eval]
  | fls => rfl
  | impl p q => simp [neg, eval]
  | ist c p => simp [neg, eval]

/-- Two valuations agreeing on atoms and on modal atoms are equal. -/
theorem cval_ext {v w : CVal A C} (ha : v.atom = w.atom) (hi : v.ist = w.ist) :
    v = w := by
  obtain ⟨a1, i1⟩ := v
  obtain ⟨a2, i2⟩ := w
  simp_all

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

/-- The base language: no context machinery.  This is the paper's `L` inside
`L⁺`. -/
def IsBase : CForm A C → Prop
  | .lit _ _ => True
  | .fls => True
  | .impl p q => IsBase p ∧ IsBase q
  | .ist _ _ => False

/-! ## Substitution -/

/-- Homomorphic extension of an atom substitution.  A negative literal goes to
the negation of the image of its atom. -/
def subst (s : A → CForm A C) : CForm A C → CForm A C
  | .lit a b => bif b then neg (s a) else s a
  | .fls => .fls
  | .impl p q => .impl (subst s p) (subst s q)
  | .ist c p => .ist c (subst s p)

/-- The valuation a substitution pulls back: read an atom through `s`, and a
modal atom through its substituted form. -/
def pullback (v : CVal A C) (s : A → CForm A C) : CVal A C where
  atom a := eval v (s a)
  ist c p := v.ist c (subst s p)

/-- The substitution replacing each atom by its truth value in `M`. -/
def boolSubst (M : CVal A C) : A → CForm A C :=
  fun a => bif M.atom a then CForm.tru else CForm.fls

/-- A set of consequents is proposition-uniform when it is closed under
substitution. -/
def PropUniform (Γ : Set (CForm A C)) : Prop :=
  ∀ (s : A → CForm A C), ∀ p ∈ Γ, subst s p ∈ Γ

/-! ## Default rules and Reiter extensions -/

/-- A default rule `α : β / γ`. -/
structure Rule (A C : Type) where
  /-- The prerequisite. -/
  prereq : CForm A C
  /-- The justification. -/
  justif : CForm A C
  /-- The consequent. -/
  conseq : CForm A C

/-- The rules of `S` that fire against `X`, given the candidate extension
`E` against which justifications are tested. -/
def fired (S : Set (Rule A C)) (E X : Set (CForm A C)) : Set (CForm A C) :=
  {γ | ∃ r ∈ S, r.conseq = γ ∧ r.prereq ∈ X ∧ neg r.justif ∉ E}

/-- The stages of the Reiter construction, tested against a candidate `E`. -/
def stage (T : Set (CForm A C)) (S : Set (Rule A C)) (E : Set (CForm A C)) :
    ℕ → Set (CForm A C)
  | 0 => Cn T
  | (i + 1) => Cn (stage T S E i) ∪ fired S E (stage T S E i)

/-- `E` is an extension of `(T, S)` when it is the fixed point of its own
stage construction. -/
def IsExtension (T : Set (CForm A C)) (S : Set (Rule A C))
    (E : Set (CForm A C)) : Prop :=
  E = ⋃ i, stage T S E i

/-- A schema is monotone when every justification is `⊤`. -/
def Monotone (S : Set (Rule A C)) : Prop := ∀ r ∈ S, r.justif = CForm.tru

/-! ## Logical automorphisms -/

/-- A bijection of the context language realised by a bijection of valuations
and commuting with negation. -/
structure LogAut (A C : Type) where
  /-- The action on formulas. -/
  form : CForm A C ≃ CForm A C
  /-- The action on valuations. -/
  val : CVal A C ≃ CVal A C
  /-- The two actions agree, in the sense of the substitution lemma. -/
  eval_form : ∀ (v : CVal A C) (p : CForm A C), eval v (form p) = eval (val v) p
  /-- The action is a homomorphism for negation. -/
  form_neg : ∀ p : CForm A C, form (neg p) = neg (form p)

namespace LogAut

variable (e : LogAut A C)

/-- The preimage of a theory. -/
def pre (E : Set (CForm A C)) : Set (CForm A C) := (⇑e.form) ⁻¹' E

@[simp] theorem mem_pre {E : Set (CForm A C)} {p : CForm A C} :
    p ∈ e.pre E ↔ e.form p ∈ E := Iff.rfl

/-- The action on rules, componentwise. -/
def mapRule (r : Rule A C) : Rule A C :=
  ⟨e.form r.prereq, e.form r.justif, e.form r.conseq⟩

/-- The inverse action on rules. -/
def symmRule (r : Rule A C) : Rule A C :=
  ⟨e.form.symm r.prereq, e.form.symm r.justif, e.form.symm r.conseq⟩

/-- The preimage of a set of rules. -/
def preRules (S : Set (Rule A C)) : Set (Rule A C) := {r | e.mapRule r ∈ S}

end LogAut

/-! ## The shift

The frame map is an equivalence of the context type; the bi-infinite frame is
the motivating case. -/

section Shift

variable (oc : C ≃ C)

/-- The shift on formulas: relabel every context index by `oc`. -/
def shift : CForm A C → CForm A C
  | .lit a b => .lit a b
  | .fls => .fls
  | .impl p q => .impl (shift p) (shift q)
  | .ist c p => .ist (oc c) (shift p)

theorem shift_symm_shift (p : CForm A C) : shift oc.symm (shift oc p) = p := by
  induction p with
  | lit a b => rfl
  | fls => rfl
  | impl p q ihp ihq => simp [shift, ihp, ihq]
  | ist c p ih => simp [shift, ih]

theorem shift_shift_symm (p : CForm A C) : shift oc (shift oc.symm p) = p := by
  induction p with
  | lit a b => rfl
  | fls => rfl
  | impl p q ihp ihq => simp [shift, ihp, ihq]
  | ist c p ih => simp [shift, ih]

/-- The shift is a bijection of formulas. -/
def shiftEquiv : CForm A C ≃ CForm A C where
  toFun := shift oc
  invFun := shift oc.symm
  left_inv := shift_symm_shift oc
  right_inv := shift_shift_symm oc

@[simp] theorem shift_neg (p : CForm A C) :
    shift oc (neg p) = neg (shift oc p) := by
  cases p <;> rfl

/-- The valuation the shift pulls back. -/
def shiftVal (v : CVal A C) : CVal A C where
  atom := v.atom
  ist c p := v.ist (oc c) (shift oc p)

theorem eval_shift (v : CVal A C) (p : CForm A C) :
    eval v (shift oc p) = eval (shiftVal oc v) p := by
  induction p with
  | lit a b => rfl
  | fls => rfl
  | impl p q ihp ihq => simp [eval, shift, ihp, ihq]
  | ist c p _ => rfl

theorem shiftVal_symm_shiftVal (v : CVal A C) :
    shiftVal oc.symm (shiftVal oc v) = v := by
  refine cval_ext rfl ?_
  funext c p
  show v.ist (oc (oc.symm c)) (shift oc (shift oc.symm p)) = v.ist c p
  rw [oc.apply_symm_apply, shift_shift_symm]

theorem shiftVal_shiftVal_symm (v : CVal A C) :
    shiftVal oc (shiftVal oc.symm v) = v := by
  refine cval_ext rfl ?_
  funext c p
  show v.ist (oc.symm (oc c)) (shift oc.symm (shift oc p)) = v.ist c p
  rw [oc.symm_apply_apply, shift_symm_shift]

/-- The shift as a valuation bijection. -/
def shiftValEquiv : CVal A C ≃ CVal A C where
  toFun := shiftVal oc
  invFun := shiftVal oc.symm
  left_inv := shiftVal_symm_shiftVal oc
  right_inv := shiftVal_shiftVal_symm oc

/-- The shift, packaged as a logical automorphism. -/
def shiftAut : LogAut A C where
  form := shiftEquiv oc
  val := shiftValEquiv oc
  eval_form := eval_shift oc
  form_neg := shift_neg oc

end Shift

/-! ## Atom automorphisms

An element of `Aut(L)` is a permutation `π` of the atoms together with a sign
pattern `ε`, which may be an arbitrary function.  Context indices are fixed and
the map acts inside the scope of `ist`. -/

section Aut

theorem xor_cancel (x y : Bool) : xor (xor x y) y = x := by
  cases x <;> cases y <;> rfl

theorem xor_cancel_left (x y : Bool) : xor x (xor x y) = y := by
  cases x <;> cases y <;> rfl

theorem xor_assoc' (x y z : Bool) : xor (xor x y) z = xor x (xor y z) := by
  cases x <;> cases y <;> cases z <;> rfl

/-- The action of `(π, ε)` on formulas. -/
def autForm (π : A ≃ A) (ε : A → Bool) : CForm A C → CForm A C
  | .lit a b => .lit (π a) (xor b (ε a))
  | .fls => .fls
  | .impl p q => .impl (autForm π ε p) (autForm π ε q)
  | .ist c p => .ist c (autForm π ε p)

/-- The sign pattern of the inverse. -/
def invEps (π : A ≃ A) (ε : A → Bool) : A → Bool := fun a => ε (π.symm a)

theorem autForm_symm_autForm (π : A ≃ A) (ε : A → Bool) (p : CForm A C) :
    autForm π.symm (invEps π ε) (autForm π ε p) = p := by
  induction p with
  | lit a b => simp [autForm, invEps, Equiv.symm_apply_apply, xor_cancel]
  | fls => rfl
  | impl p q ihp ihq => simp [autForm, ihp, ihq]
  | ist c p ih => simp [autForm, ih]

theorem autForm_autForm_symm (π : A ≃ A) (ε : A → Bool) (p : CForm A C) :
    autForm π ε (autForm π.symm (invEps π ε) p) = p := by
  induction p with
  | lit a b => simp [autForm, invEps, Equiv.apply_symm_apply, xor_cancel]
  | fls => rfl
  | impl p q ihp ihq => simp [autForm, ihp, ihq]
  | ist c p ih => simp [autForm, ih]

/-- An atom automorphism is a genuine bijection of formulas. -/
def autFormEquiv (π : A ≃ A) (ε : A → Bool) : CForm A C ≃ CForm A C where
  toFun := autForm π ε
  invFun := autForm π.symm (invEps π ε)
  left_inv := autForm_symm_autForm π ε
  right_inv := autForm_autForm_symm π ε

theorem autForm_neg (π : A ≃ A) (ε : A → Bool) (p : CForm A C) :
    autForm π ε (neg p) = neg (autForm π ε p) := by
  cases p with
  | lit a b => cases b <;> cases h : ε a <;> simp [autForm, h]
  | fls => rfl
  | impl p q => rfl
  | ist c p => rfl

/-- The valuation an atom automorphism pulls back. -/
def autVal (π : A ≃ A) (ε : A → Bool) (v : CVal A C) : CVal A C where
  atom a := xor (ε a) (v.atom (π a))
  ist c p := v.ist c (autForm π ε p)

theorem eval_autForm (π : A ≃ A) (ε : A → Bool) (v : CVal A C) (p : CForm A C) :
    eval v (autForm π ε p) = eval (autVal π ε v) p := by
  induction p with
  | lit a b => simp [autForm, eval, autVal, xor_assoc']
  | fls => rfl
  | impl p q ihp ihq => simp [eval, autForm, ihp, ihq]
  | ist c p _ => rfl

theorem autVal_symm_autVal (π : A ≃ A) (ε : A → Bool) (v : CVal A C) :
    autVal π.symm (invEps π ε) (autVal π ε v) = v := by
  refine cval_ext ?_ ?_
  · funext a
    simp [autVal, invEps, Equiv.apply_symm_apply, xor_cancel_left]
  · funext c p
    show v.ist c (autForm π ε (autForm π.symm (invEps π ε) p)) = v.ist c p
    rw [autForm_autForm_symm]

theorem autVal_autVal_symm (π : A ≃ A) (ε : A → Bool) (v : CVal A C) :
    autVal π ε (autVal π.symm (invEps π ε) v) = v := by
  refine cval_ext ?_ ?_
  · funext a
    simp [autVal, invEps, Equiv.symm_apply_apply]
  · funext c p
    show v.ist c (autForm π.symm (invEps π ε) (autForm π ε p)) = v.ist c p
    rw [autForm_symm_autForm]

/-- and a bijection of valuations. -/
def autValEquiv (π : A ≃ A) (ε : A → Bool) : CVal A C ≃ CVal A C where
  toFun := autVal π ε
  invFun := autVal π.symm (invEps π ε)
  left_inv := autVal_symm_autVal π ε
  right_inv := autVal_autVal_symm π ε

/-- An atom automorphism, packaged as a logical automorphism. -/
def autAut (π : A ≃ A) (ε : A → Bool) : LogAut A C where
  form := autFormEquiv π ε
  val := autValEquiv π ε
  eval_form := eval_autForm π ε
  form_neg := autForm_neg π ε

/-- The group `Aut(L)`, as a set of logical automorphisms. -/
def AutL (A C : Type) : Set (LogAut A C) :=
  {g | ∃ (π : A ≃ A) (ε : A → Bool), g = autAut π ε}

/-- An atom automorphism, read as a substitution. -/
def autSubst (π : A ≃ A) (ε : A → Bool) : A → CForm A C :=
  fun a => CForm.lit (π a) (ε a)

/-- The action of a substitution on a rule. -/
def substRule (s : A → CForm A C) (r : Rule A C) : Rule A C :=
  ⟨subst s r.prereq, subst s r.justif, subst s r.conseq⟩

/-- A schema is proposition-uniform when its rules are closed under every
substitution. -/
def PropUniformRules (S : Set (Rule A C)) : Prop :=
  ∀ (s : A → CForm A C), ∀ r ∈ S, substRule s r ∈ S

/-- `T` is symmetric under `G` when the group moves any model of `T` to any
other.  Only the atoms matter, since `T` and the sentences at issue lie in the
base language. -/
def SymmetricUnder (G : Set (LogAut A C)) (T : Set (CForm A C)) : Prop :=
  ∀ M N : CVal A C, Models T M → Models T N →
    ∃ g ∈ G, (g.val.symm M).atom = N.atom

end Aut

/-! ## The copy schema -/

/-- The consequents of the copy schema: `ist c p → p`. -/
def copySchema (A C : Type) : Set (CForm A C) :=
  {q | ∃ (c : C) (p : CForm A C), q = CForm.impl (CForm.ist c p) p}

/-- The copy schema as a set of default rules: `⊤ : ⊤ / (ist c p → p)`. -/
def copyRules (A C : Type) : Set (Rule A C) :=
  {r | ∃ (c : C) (p : CForm A C),
    r = ⟨CForm.tru, CForm.tru, CForm.impl (CForm.ist c p) p⟩}

/-- The canonical evaluation, in which `ist c p` says exactly what `p` says. -/
def canon (atomv : A → Bool) : CForm A C → Bool
  | .lit a b => xor b (atomv a)
  | .fls => false
  | .impl p q => !(canon atomv p) || canon atomv q
  | .ist _ p => canon atomv p

/-- The valuation built from the canonical evaluation. -/
def canonVal (atomv : A → Bool) : CVal A C where
  atom := atomv
  ist := fun _ p => canon atomv p

end TranscendenceTower.UniformityPlatform
