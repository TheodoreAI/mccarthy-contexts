/-
  Rigidity: a context-uniform schema has a shift-invariant extension.

  The result is that a unique consistent extension `E` satisfies `σ⁻¹(E) = E`,
  so the levels of the tower are indistinguishable from one another.

  Three things about this development are worth stating up front, two of them
  corrections to the paper.

  * The proof is organised around an arbitrary *logical automorphism* of the
    context language rather than around the shift specifically; the shift is
    then one instance.  The other intended instance is the action of an atom
    permutation, which is Step 1 of the trichotomy.  That step and this
    theorem are literally the same lemma, `LogAut.isExtension_pre`.

  * The consequence drawn in the paper,
      `ist c φ ∈ E ↔ ist (out c) φ ∈ E`,
    is false as stated.  The shift relabels the context indices *inside* `φ`
    as well, so what `σ⁻¹(E) = E` delivers is
      `ist c φ ∈ E ↔ ist (out c) (σ φ) ∈ E`,
    with the unshifted form recovered exactly on the base language, where `σ`
    is the identity.  Both appear below, as `rigidity_ist` and
    `rigidity_ist_base`.

  * The frame map is required to be a *bijection*, not merely an injection.
    This is not a convenience.  Surjectivity is used in two places: in
    `LogAut.Cn_pre`, where every model of `σ⁻¹(X)` must be the image of a
    model of `X`, and in `LogAut.stage_pre`, where a rule of `S` is pulled
    back along the shift.  With `out` merely injective a rule whose consequent
    lies outside the image of `σ` has no preimage to fire, and the stagewise
    correspondence breaks.  The paper passes over this in the clause
    "groundedness is inherited stagewise by the same argument".  Nothing here
    shows the injective case is false; it shows this argument does not reach
    it.  The paper's own remark on the definable-`c₀` loophole singles out the
    bijective (bi-infinite) frame as the one carrying the content, so this is
    the intended case.
-/

import Development.Uniformity

set_option autoImplicit false

namespace TranscendenceTower.Uniformity

variable {A C : Type}

/-! ## Negation, and two facts about consequence -/

/-- Negation, in the `→`/`⊥` fragment. -/
def Neg (p : CForm A C) : CForm A C := CForm.impl p CForm.fls

@[simp] theorem eval_Neg (v : CVal A C) (p : CForm A C) :
    eval v (Neg p) = !(eval v p) := by
  simp [Neg, eval]

theorem Cn_mono {X Y : Set (CForm A C)} (h : X ⊆ Y) : Cn X ⊆ Cn Y :=
  fun _ hp v hv => hp v fun q hq => hv q (h hq)

theorem Cn_idem (X : Set (CForm A C)) : Cn (Cn X) = Cn X :=
  Set.Subset.antisymm
    (fun _ hp v hv => hp v fun q hq => hq v hv)
    (subset_Cn _)

theorem models_Cn {X : Set (CForm A C)} {v : CVal A C} (hv : Models X v) :
    Models (Cn X) v := fun _ hq => hq v hv

/-- Valuations are determined on the base language by their atoms. -/
theorem eval_base_congr {v w : CVal A C} (h : v.atom = w.atom) :
    ∀ p : CForm A C, IsBase p → eval v p = eval w p := by
  intro p
  induction p with
  | atom a => intro _; simp [eval, h]
  | fls => intro _; rfl
  | impl p q ihp ihq => intro hb; simp [eval, ihp hb.1, ihq hb.2]
  | ist c p _ => intro hb; exact hb.elim

/-! ## Default rules and Reiter extensions

The paper's definition, transcribed.  A rule fires at stage `i + 1` when its
prerequisite is already in stage `i` and the negation of its justification is
absent from the candidate `E` being tested.  The self-reference through `E` is
what makes an extension a fixed point rather than a closure. -/

/-- A default rule `α : β / γ`. -/
structure Rule (A C : Type) where
  /-- The prerequisite. -/
  prereq : CForm A C
  /-- The justification. -/
  justif : CForm A C
  /-- The consequent. -/
  conseq : CForm A C

/-- The rules of `S` that fire against `X` given the candidate `E`. -/
def fired (S : Set (Rule A C)) (E X : Set (CForm A C)) : Set (CForm A C) :=
  {γ | ∃ r ∈ S, r.conseq = γ ∧ r.prereq ∈ X ∧ Neg r.justif ∉ E}

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

/-! ## Logical automorphisms

A logical automorphism is a bijection of formulas realised on valuations:
composing with it is the same as evaluating against a transformed valuation.
This is the pattern of the substitution lemma in `Uniformity.lean`, with the
difference that both maps are required to be invertible. -/

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
  form_neg : ∀ p : CForm A C, form (Neg p) = Neg (form p)

namespace LogAut

variable (e : LogAut A C)

/-- The preimage of a theory: the paper's `σ⁻¹(E)`. -/
def pre (E : Set (CForm A C)) : Set (CForm A C) := (⇑e.form) ⁻¹' E

@[simp] theorem mem_pre {E : Set (CForm A C)} {p : CForm A C} :
    p ∈ e.pre E ↔ e.form p ∈ E := Iff.rfl

theorem pre_union (X Y : Set (CForm A C)) : e.pre (X ∪ Y) = e.pre X ∪ e.pre Y :=
  Set.preimage_union

theorem pre_iUnion (f : ℕ → Set (CForm A C)) :
    e.pre (⋃ i, f i) = ⋃ i, e.pre (f i) := Set.preimage_iUnion

/-- The action on rules, componentwise. -/
def mapRule (r : Rule A C) : Rule A C :=
  ⟨e.form r.prereq, e.form r.justif, e.form r.conseq⟩

/-- The inverse action on rules. -/
def symmRule (r : Rule A C) : Rule A C :=
  ⟨e.form.symm r.prereq, e.form.symm r.justif, e.form.symm r.conseq⟩

@[simp] theorem mapRule_symmRule (r : Rule A C) : e.mapRule (e.symmRule r) = r := by
  simp [mapRule, symmRule]

/-- The preimage of a set of rules: the paper's `σ⁻¹(S_F)`. -/
def preRules (S : Set (Rule A C)) : Set (Rule A C) := {r | e.mapRule r ∈ S}

/-! ### Transport of semantics -/

/-- Models transport forwards along `val`. -/
theorem models_val {X : Set (CForm A C)} {v : CVal A C} (hv : Models X v) :
    Models (e.pre X) (e.val v) := by
  intro q hq
  rw [← e.eval_form]
  exact hv _ hq

/-- and backwards, which is where invertibility is used. -/
theorem models_val_symm {X : Set (CForm A C)} {w : CVal A C}
    (hw : Models (e.pre X) w) : Models X (e.val.symm w) := by
  intro q hq
  have hp : e.form (e.form.symm q) = q := e.form.apply_symm_apply q
  have hmem : e.form.symm q ∈ e.pre X := by rw [mem_pre, hp]; exact hq
  have h := hw _ hmem
  rw [← e.val.apply_symm_apply w, ← e.eval_form, hp] at h
  exact h

/-- **Consequence commutes with the automorphism.**  The first inclusion holds
for any substitution; the second needs every model of `σ⁻¹(X)` to be the image
of a model of `X`, which is exactly what surjectivity buys. -/
theorem Cn_pre (X : Set (CForm A C)) : Cn (e.pre X) = e.pre (Cn X) := by
  ext p
  constructor
  · intro hp v hv
    rw [e.eval_form]
    exact hp _ (e.models_val hv)
  · intro hp w hw
    have h := hp (e.val.symm w) (e.models_val_symm hw)
    rw [e.eval_form, e.val.apply_symm_apply] at h
    exact h

/-- Consistency transports. -/
theorem consistent_pre {X : Set (CForm A C)} (h : Consistent X) :
    Consistent (e.pre X) := by
  obtain ⟨v, hv⟩ := h
  exact ⟨e.val v, e.models_val hv⟩

/-! ### Transport of the fixed-point construction -/

variable {T : Set (CForm A C)} {S : Set (Rule A C)}

/-- A theory fixed pointwise is fixed as a set. -/
theorem pre_eq_of_fixed (hT : ∀ p ∈ T, e.form p = p) : e.pre T = T := by
  ext p
  constructor
  · intro hp
    have hp' : e.form p ∈ T := hp
    have h : e.form p = p := e.form.injective (hT _ hp')
    rwa [h] at hp'
  · intro hp
    rw [mem_pre, hT p hp]
    exact hp

/-- The firing set transports. -/
theorem fired_pre (hS : e.preRules S = S) (E X : Set (CForm A C)) :
    fired S (e.pre E) (e.pre X) = e.pre (fired S E X) := by
  ext γ
  constructor
  · rintro ⟨r, hr, rfl, hprereq, hjust⟩
    refine ⟨e.mapRule r, ?_, rfl, hprereq, ?_⟩
    · rw [← hS] at hr; exact hr
    · have hj : e.form (Neg r.justif) ∉ E := hjust
      rw [e.form_neg] at hj
      simpa [mapRule] using hj
  · rintro ⟨r, hr, hconseq, hprereq, hjust⟩
    refine ⟨e.symmRule r, ?_, ?_, ?_, ?_⟩
    · rw [← hS]
      show e.mapRule (e.symmRule r) ∈ S
      rw [mapRule_symmRule]; exact hr
    · show e.form.symm r.conseq = γ
      rw [hconseq]; exact e.form.symm_apply_apply γ
    · show e.form (e.form.symm r.prereq) ∈ X
      rw [e.form.apply_symm_apply]; exact hprereq
    · show Neg (e.form.symm r.justif) ∉ e.pre E
      rw [mem_pre, e.form_neg, e.form.apply_symm_apply]
      exact hjust

/-- Each stage of the construction for `σ⁻¹(E)` is the preimage of the
corresponding stage for `E`. -/
theorem stage_pre (hT : ∀ p ∈ T, e.form p = p) (hS : e.preRules S = S)
    (E : Set (CForm A C)) :
    ∀ i, stage T S (e.pre E) i = e.pre (stage T S E i) := by
  intro i
  induction i with
  | zero =>
    show Cn T = e.pre (Cn T)
    rw [← e.Cn_pre, e.pre_eq_of_fixed hT]
  | succ i ih =>
    show Cn (stage T S (e.pre E) i) ∪ fired S (e.pre E) (stage T S (e.pre E) i)
        = e.pre (Cn (stage T S E i) ∪ fired S E (stage T S E i))
    rw [ih, e.Cn_pre, e.fired_pre hS, e.pre_union]

/-- **The transport lemma.**  An automorphism fixing the base theory pointwise
and preserving the schema carries extensions to extensions.  Instantiated at
the shift this is rigidity; instantiated at an atom permutation it is Step 1 of
the trichotomy. -/
theorem isExtension_pre (hT : ∀ p ∈ T, e.form p = p) (hS : e.preRules S = S)
    {E : Set (CForm A C)} (hE : IsExtension T S E) :
    IsExtension T S (e.pre E) := by
  show e.pre E = ⋃ i, stage T S (e.pre E) i
  simp only [e.stage_pre hT hS E]
  rw [← e.pre_iUnion]
  exact congrArg _ hE

end LogAut

/-! ## The shift

The frame map is an equivalence `oc : C ≃ C`; the bi-infinite frame is the
motivating case.  Everything below is the shift packaged as a `LogAut`. -/

section Shift

variable (oc : C ≃ C)

/-- The shift on formulas: relabel every context index by `oc`. -/
def shift : CForm A C → CForm A C
  | .atom a => .atom a
  | .fls => .fls
  | .impl p q => .impl (shift p) (shift q)
  | .ist c p => .ist (oc c) (shift p)

@[simp] theorem shift_neg (p : CForm A C) : shift oc (Neg p) = Neg (shift oc p) := rfl

theorem shift_symm_shift (p : CForm A C) : shift oc.symm (shift oc p) = p := by
  induction p with
  | atom a => rfl
  | fls => rfl
  | impl p q ihp ihq => simp [shift, ihp, ihq]
  | ist c p ih => simp [shift, ih]

theorem shift_shift_symm (p : CForm A C) : shift oc (shift oc.symm p) = p := by
  induction p with
  | atom a => rfl
  | fls => rfl
  | impl p q ihp ihq => simp [shift, ihp, ihq]
  | ist c p ih => simp [shift, ih]

/-- The shift is a bijection of formulas. -/
def shiftEquiv : CForm A C ≃ CForm A C where
  toFun := shift oc
  invFun := shift oc.symm
  left_inv := shift_symm_shift oc
  right_inv := shift_shift_symm oc

/-- The shift acts as the identity on the base language. -/
theorem shift_base : ∀ p : CForm A C, IsBase p → shift oc p = p := by
  intro p
  induction p with
  | atom a => intro _; rfl
  | fls => intro _; rfl
  | impl p q ihp ihq => intro hb; simp [shift, ihp hb.1, ihq hb.2]
  | ist c p _ => intro hb; exact hb.elim

/-- The valuation the shift pulls back. -/
def shiftVal (v : CVal A C) : CVal A C where
  atom := v.atom
  ist c p := v.ist (oc c) (shift oc p)

theorem eval_shift (v : CVal A C) (p : CForm A C) :
    eval v (shift oc p) = eval (shiftVal oc v) p := by
  induction p with
  | atom a => rfl
  | fls => rfl
  | impl p q ihp ihq => simp [eval, shift, ihp, ihq]
  | ist c p _ => rfl

theorem cval_ext {v w : CVal A C} (ha : v.atom = w.atom) (hi : v.ist = w.ist) :
    v = w := by
  obtain ⟨a1, i1⟩ := v
  obtain ⟨a2, i2⟩ := w
  simp_all

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

/-! ## Rigidity -/

variable {T : Set (CForm A C)} {S : Set (Rule A C)} {E : Set (CForm A C)}

/-- **Rigidity.**  A context-uniform schema over a context-free base theory has
a shift-invariant unique consistent extension. -/
theorem rigidity
    (hT : ∀ p ∈ T, IsBase p)
    (hS : (shiftAut (A := A) oc).preRules S = S)
    (hE : IsExtension T S E) (hcon : Consistent E)
    (huniq : ∀ E', IsExtension T S E' → Consistent E' → E' = E) :
    (shiftAut (A := A) oc).pre E = E :=
  huniq _
    (LogAut.isExtension_pre _ (fun p hp => shift_base oc p (hT p hp)) hS hE)
    (LogAut.consistent_pre _ hcon)

/-- The corrected consequence: the right-hand side carries the shift.  This is
what `σ⁻¹(E) = E` actually says about the levels. -/
theorem rigidity_ist (h : (shiftAut (A := A) oc).pre E = E) (c : C)
    (φ : CForm A C) :
    CForm.ist c φ ∈ E ↔ CForm.ist (oc c) (shift oc φ) ∈ E := by
  constructor
  · intro hmem
    have : CForm.ist c φ ∈ (shiftAut (A := A) oc).pre E := by rw [h]; exact hmem
    exact this
  · intro hmem
    have : CForm.ist c φ ∈ (shiftAut (A := A) oc).pre E := hmem
    rwa [h] at this

/-- On the base language the shift is invisible, and the paper's displayed
equivalence holds as written. -/
theorem rigidity_ist_base (h : (shiftAut (A := A) oc).pre E = E) (c : C)
    {φ : CForm A C} (hφ : IsBase φ) :
    CForm.ist c φ ∈ E ↔ CForm.ist (oc c) φ ∈ E := by
  rw [rigidity_ist oc h c φ, shift_base oc φ hφ]

end Shift

/-! ## Non-vacuity

The hypotheses of `rigidity` are satisfiable.  The empty schema over any
consistent base theory has `Cn T` as its unique consistent extension, so the
theorem is not about an empty class. -/

section Vacuity

variable {T : Set (CForm A C)}

@[simp] theorem fired_empty (E X : Set (CForm A C)) :
    fired (∅ : Set (Rule A C)) E X = ∅ := by
  ext γ
  simp [fired]

theorem stage_empty (E : Set (CForm A C)) :
    ∀ i, stage T (∅ : Set (Rule A C)) E i = Cn T := by
  intro i
  induction i with
  | zero => rfl
  | succ i ih =>
    show Cn (stage T (∅ : Set (Rule A C)) E i) ∪ _ = Cn T
    rw [ih, fired_empty, Set.union_empty, Cn_idem]

theorem isExtension_empty : IsExtension T (∅ : Set (Rule A C)) (Cn T) := by
  show Cn T = ⋃ i, stage T (∅ : Set (Rule A C)) (Cn T) i
  simp [stage_empty, Set.iUnion_const]

theorem unique_empty (E' : Set (CForm A C))
    (h : IsExtension T (∅ : Set (Rule A C)) E') : E' = Cn T := by
  rw [h]
  simp [stage_empty, Set.iUnion_const]

theorem consistent_Cn (h : Consistent T) : Consistent (Cn T) := by
  obtain ⟨v, hv⟩ := h
  exact ⟨v, models_Cn hv⟩

/-- The hypotheses of `rigidity` hold for the empty schema, and the conclusion
is the expected one. -/
theorem rigidity_empty (oc : C ≃ C) (hT : ∀ p ∈ T, IsBase p)
    (hcon : Consistent T) :
    (shiftAut (A := A) oc).pre (Cn T) = Cn T :=
  rigidity oc hT
    (by ext r; simp [LogAut.preRules])
    isExtension_empty (consistent_Cn hcon)
    (fun E' hE' _ => unique_empty E' hE')

end Vacuity

/-! ## Monotone schemas, and the copy

The paper asserts without proof that a monotone schema has at most one
extension.  That is `monotone_unique` below: when every justification is `⊤`
the consistency test never fails, so the stages stop depending on the candidate
and the fixed point is forced.

The copy schema is then a genuine instance of `rigidity`: it is monotone,
consistent, and context-uniform, so its unique extension is shift-invariant.
This is the paper's closing corollary, that the forced outcome of treating
contexts uniformly is McCarthy's "pointless version". -/

section Monotone

variable {T : Set (CForm A C)} {S : Set (Rule A C)}

/-- A schema is monotone when every justification is `⊤`. -/
def Monotone (S : Set (Rule A C)) : Prop := ∀ r ∈ S, r.justif = CForm.tru

/-- A consistent theory cannot contain `¬⊤`, so a monotone rule always fires. -/
theorem neg_tru_not_mem {E : Set (CForm A C)} (h : Consistent E) :
    Neg CForm.tru ∉ E := by
  obtain ⟨v, hv⟩ := h
  intro hmem
  have := hv _ hmem
  simp [Neg, eval] at this

/-- For a monotone schema the stages do not depend on the candidate. -/
theorem stage_monotone (hmono : Monotone S) {E : Set (CForm A C)}
    (hE : Neg CForm.tru ∉ E) :
    ∀ i, stage T S E i = stage T S (∅ : Set (CForm A C)) i := by
  intro i
  induction i with
  | zero => rfl
  | succ i ih =>
    show Cn (stage T S E i) ∪ fired S E (stage T S E i)
        = Cn (stage T S ∅ i) ∪ fired S ∅ (stage T S ∅ i)
    rw [ih]
    congr 1
    ext γ
    constructor
    · rintro ⟨r, hr, hc, hp, _⟩
      exact ⟨r, hr, hc, hp, by simp⟩
    · rintro ⟨r, hr, hc, hp, _⟩
      refine ⟨r, hr, hc, hp, ?_⟩
      rw [hmono r hr]
      exact hE

/-- **A monotone schema has at most one consistent extension.** -/
theorem monotone_unique (hmono : Monotone S) {E E' : Set (CForm A C)}
    (hE : IsExtension T S E) (hcE : Consistent E)
    (hE' : IsExtension T S E') (hcE' : Consistent E') : E' = E := by
  rw [hE, hE']
  simp only [stage_monotone hmono (neg_tru_not_mem hcE),
    stage_monotone hmono (neg_tru_not_mem hcE')]

/-- and exactly one, as soon as the candidate is consistent. -/
theorem isExtension_monotone (hmono : Monotone S)
    (hc : Consistent (⋃ i, stage T S (∅ : Set (CForm A C)) i)) :
    IsExtension T S (⋃ i, stage T S (∅ : Set (CForm A C)) i) := by
  show _ = ⋃ i, stage T S (⋃ i, stage T S (∅ : Set (CForm A C)) i) i
  simp only [stage_monotone hmono (neg_tru_not_mem hc)]

end Monotone

section Copy

variable (A C)

/-- The copy schema as a set of default rules: `⊤ : ⊤ / (ist c p → p)`. -/
def copyRules : Set (Rule A C) :=
  {r | ∃ (c : C) (p : CForm A C),
    r = ⟨CForm.tru, CForm.tru, CForm.impl (CForm.ist c p) p⟩}

variable {A C}

theorem copyRules_monotone : Monotone (copyRules A C) := by
  rintro r ⟨c, p, rfl⟩
  rfl

@[simp] theorem shift_tru (oc : C ≃ C) : shift oc (CForm.tru : CForm A C) = CForm.tru := rfl

/-- The copy schema is context-uniform: it is its own preimage under the
shift. -/
theorem copyRules_contextUniform (oc : C ≃ C) :
    (shiftAut (A := A) oc).preRules (copyRules A C) = copyRules A C := by
  ext r
  constructor
  · rintro ⟨c, p, hr⟩
    obtain ⟨pre, just, con⟩ := r
    have h1 : shift oc pre = CForm.tru := congrArg Rule.prereq hr
    have h2 : shift oc just = CForm.tru := congrArg Rule.justif hr
    have h3 : shift oc con = CForm.impl (CForm.ist c p) p := congrArg Rule.conseq hr
    refine ⟨oc.symm c, shift oc.symm p, ?_⟩
    have e1 : pre = CForm.tru := by
      have := congrArg (shift oc.symm) h1
      rwa [shift_symm_shift] at this
    have e2 : just = CForm.tru := by
      have := congrArg (shift oc.symm) h2
      rwa [shift_symm_shift] at this
    have e3 : con = CForm.impl (CForm.ist (oc.symm c) (shift oc.symm p))
        (shift oc.symm p) := by
      have := congrArg (shift oc.symm) h3
      rwa [shift_symm_shift] at this
    simp [e1, e2, e3]
  · rintro ⟨c, p, rfl⟩
    exact ⟨oc c, shift oc p, rfl⟩

/-- The canonical valuation models every stage of the copy construction. -/
theorem canonVal_models_stage (atomv : A → Bool) :
    ∀ i, Models (stage (∅ : Set (CForm A C)) (copyRules A C) ∅ i) (canonVal atomv) := by
  intro i
  induction i with
  | zero =>
    exact models_Cn (fun q hq => hq.elim)
  | succ i ih =>
    intro q hq
    rcases hq with hq | hq
    · exact models_Cn ih q hq
    · obtain ⟨r, ⟨c, p, rfl⟩, hc, _, _⟩ := hq
      have : q ∈ copySchema A C := ⟨c, p, hc.symm⟩
      exact copySchema_consistent atomv q this

/-- **The copy schema satisfies every hypothesis of `rigidity`.**  Its unique
consistent extension is shift-invariant, and on the base language the levels
agree literally. -/
theorem rigidity_copy (oc : C ≃ C) (atomv : A → Bool) :
    (shiftAut (A := A) oc).pre
        (⋃ i, stage (∅ : Set (CForm A C)) (copyRules A C) ∅ i)
      = ⋃ i, stage (∅ : Set (CForm A C)) (copyRules A C) ∅ i := by
  have hc : Consistent (⋃ i, stage (∅ : Set (CForm A C)) (copyRules A C) ∅ i) := by
    refine ⟨canonVal atomv, ?_⟩
    intro q hq
    obtain ⟨i, hi⟩ := Set.mem_iUnion.mp hq
    exact canonVal_models_stage atomv i q hi
  exact rigidity oc (fun p hp => hp.elim) (copyRules_contextUniform oc)
    (isExtension_monotone copyRules_monotone hc) hc
    (fun E' hE' hcE' =>
      monotone_unique copyRules_monotone (isExtension_monotone copyRules_monotone hc)
        hc hE' hcE')

end Copy

section Verification

#print axioms LogAut.Cn_pre
#print axioms LogAut.isExtension_pre
#print axioms rigidity
#print axioms rigidity_ist
#print axioms rigidity_ist_base
#print axioms rigidity_empty
#print axioms monotone_unique
#print axioms rigidity_copy

end Verification

end TranscendenceTower.Uniformity
