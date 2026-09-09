import Definitions.Def_TranscendenceTowerContextUniformity

set_option autoImplicit false
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

namespace TranscendenceTower.UniformityPlatform

variable {A C : Type}


/-! ## The context language -/

namespace CForm


end CForm


/-! ## The base language -/

theorem isBase_neg {p : CForm A C} (h : IsBase p) : IsBase (neg p) := by
  cases p with
  | lit a b => trivial
  | fls => exact ⟨trivial, trivial⟩
  | impl p q => exact ⟨h, trivial⟩
  | ist c p => exact h.elim

/-! ## Substitution

Substitutions act on atoms and are extended homomorphically, acting inside
the scope of `ist`.  A negative literal is sent to the negation of the image
of its atom.  This is the paper's proposition-uniformity apparatus. -/

/-- **The substitution lemma.**  Evaluating a substituted formula is
evaluating the original against the pulled-back valuation. -/
theorem eval_subst (v : CVal A C) (s : A → CForm A C) (p : CForm A C) :
    eval v (subst s p) = eval (pullback v s) p := by
  induction p with
  | lit a b => cases b <;> simp [subst, eval, pullback]
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

/-- On the base language, the frozen substitution evaluates to `M`
regardless of the ambient valuation: every atom has become a constant. -/
theorem eval_boolSubst (M v : CVal A C) :
    ∀ p : CForm A C, IsBase p → eval v (subst (boolSubst M) p) = eval M p := by
  intro p
  induction p with
  | lit a b =>
    intro _
    cases h : M.atom a <;> cases b <;> simp [subst, boolSubst, h, eval]
  | fls => intro _; rfl
  | impl p q ihp ihq =>
    intro hb
    simp [subst, eval, ihp hb.1, ihq hb.2]
  | ist c p _ => intro hb; exact hb.elim

/-! ## The monotone dichotomy -/

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

theorem copySchema_propUniform : PropUniform (copySchema A C) := by
  rintro s q ⟨c, p, rfl⟩
  exact ⟨c, subst s p, rfl⟩

theorem eval_canonVal (atomv : A → Bool) (p : CForm A C) :
    eval (canonVal atomv) p = canon atomv p := by
  induction p with
  | lit a b => rfl
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


end Verification





/-! ## Two facts about consequence -/

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
  | lit a b => intro _; simp [eval, h]
  | fls => intro _; rfl
  | impl p q ihp ihq => intro hb; simp [eval, ihp hb.1, ihq hb.2]
  | ist c p _ => intro hb; exact hb.elim

/-! ## Default rules and Reiter extensions

The paper's definition, transcribed.  A rule fires at stage `i + 1` when its
prerequisite is already in stage `i` and the negation of its justification is
absent from the candidate `E` being tested.  The self-reference through `E` is
what makes an extension a fixed point rather than a closure. -/

/-! ## Logical automorphisms

A logical automorphism is a bijection of formulas realised on valuations:
composing with it is the same as evaluating against a transformed valuation.
This is the pattern of the substitution lemma in `Uniformity.lean`, with the
difference that both maps are required to be invertible. -/

namespace LogAut

variable (e : LogAut A C)

theorem pre_union (X Y : Set (CForm A C)) : e.pre (X ∪ Y) = e.pre X ∪ e.pre Y :=
  Set.preimage_union

theorem pre_iUnion (f : ℕ → Set (CForm A C)) :
    e.pre (⋃ i, f i) = ⋃ i, e.pre (f i) := Set.preimage_iUnion

@[simp] theorem mapRule_symmRule (r : Rule A C) : e.mapRule (e.symmRule r) = r := by
  simp [mapRule, symmRule]

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
    · have hj : e.form (neg r.justif) ∉ E := hjust
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
    · show neg (e.form.symm r.justif) ∉ e.pre E
      rw [mem_pre, e.form_neg, e.form.apply_symm_apply]
      exact hjust

/-- A base theory fixed pointwise is preserved as a closed theory.  This is
the shift's situation; the trichotomy supplies the weaker hypothesis directly,
since an atom permutation does not fix `T` formula by formula. -/
theorem pre_Cn_eq_of_fixed (hT : ∀ p ∈ T, e.form p = p) : e.pre (Cn T) = Cn T := by
  rw [← e.Cn_pre, e.pre_eq_of_fixed hT]

/-- Each stage of the construction for `σ⁻¹(E)` is the preimage of the
corresponding stage for `E`. -/
theorem stage_pre (hT : e.pre (Cn T) = Cn T) (hS : e.preRules S = S)
    (E : Set (CForm A C)) :
    ∀ i, stage T S (e.pre E) i = e.pre (stage T S E i) := by
  intro i
  induction i with
  | zero =>
    show Cn T = e.pre (Cn T)
    exact hT.symm
  | succ i ih =>
    show Cn (stage T S (e.pre E) i) ∪ fired S (e.pre E) (stage T S (e.pre E) i)
        = e.pre (Cn (stage T S E i) ∪ fired S E (stage T S E i))
    rw [ih, e.Cn_pre, e.fired_pre hS, e.pre_union]

/-- **The transport lemma.**  An automorphism fixing the base theory pointwise
and preserving the schema carries extensions to extensions.  Instantiated at
the shift this is rigidity; instantiated at an atom permutation it is Step 1 of
the trichotomy. -/
theorem isExtension_pre (hT : e.pre (Cn T) = Cn T) (hS : e.preRules S = S)
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

/-- The shift acts as the identity on the base language. -/
theorem shift_base : ∀ p : CForm A C, IsBase p → shift oc p = p := by
  intro p
  induction p with
  | lit a b => intro _; rfl
  | fls => intro _; rfl
  | impl p q ihp ihq => intro hb; simp [shift, ihp hb.1, ihq hb.2]
  | ist c p _ => intro hb; exact hb.elim

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
    (LogAut.isExtension_pre _
      (LogAut.pre_Cn_eq_of_fixed _ (fun p hp => shift_base oc p (hT p hp))) hS hE)
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

/-- A consistent theory cannot contain `¬⊤`, so a monotone rule always fires. -/
theorem neg_tru_not_mem {E : Set (CForm A C)} (h : Consistent E) :
    neg CForm.tru ∉ E := by
  obtain ⟨v, hv⟩ := h
  intro hmem
  have := hv _ hmem
  rw [eval_neg, eval_tru] at this
  simp at this

/-- For a monotone schema the stages do not depend on the candidate. -/
theorem stage_monotone (hmono : Monotone S) {E : Set (CForm A C)}
    (hE : neg CForm.tru ∉ E) :
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


end Verification





/-! ## Two facts about `xor` -/

/-! ## Atom automorphisms

An element of `Aut(L)` is given by a permutation `π` of the atoms together
with a sign pattern `ε`, which may be an arbitrary function — see the paper's
remark on why the group generated by permutations and single-atom negations is
too small to be transitive.  Context indices are fixed; the map acts inside
the scope of `ist`. -/

/-- The atom automorphisms preserve the base language. -/
theorem autForm_isBase (π : A ≃ A) (ε : A → Bool) :
    ∀ p : CForm A C, IsBase p → IsBase (autForm π ε p) := by
  intro p
  induction p with
  | lit a b => intro _; trivial
  | fls => intro _; trivial
  | impl p q ihp ihq => intro hb; exact ⟨ihp hb.1, ihq hb.2⟩
  | ist c p _ => intro hb; exact hb.elim

/-! ## Proposition-uniformity gives invariance of the schema

The paper's Step 1 asserts that `g(S) = S` follows from proposition-uniformity
because `g` is invertible.  That is exactly right, and the proof is: an atom
automorphism *is* a substitution, so uniformity gives one inclusion, and its
inverse is another substitution, which gives the other. -/

theorem autForm_eq_subst (π : A ≃ A) (ε : A → Bool) (p : CForm A C) :
    autForm π ε p = subst (autSubst π ε) p := by
  induction p with
  | lit a b => cases b <;> simp [autForm, subst, autSubst, neg]
  | fls => rfl
  | impl p q ihp ihq => simp [autForm, subst, ihp, ihq]
  | ist c p ih => simp [autForm, subst, ih]

theorem mapRule_autAut (π : A ≃ A) (ε : A → Bool) (r : Rule A C) :
    (autAut π ε).mapRule r = substRule (autSubst π ε) r := by
  simp [LogAut.mapRule, substRule, autAut, autFormEquiv, autForm_eq_subst]

/-- **Proposition-uniformity implies invariance of the schema under
`Aut(L)`.** -/
theorem preRules_autAut {S : Set (Rule A C)} (hU : PropUniformRules S)
    (π : A ≃ A) (ε : A → Bool) : (autAut π ε).preRules S = S := by
  ext r
  constructor
  · intro hr
    have hmem : (autAut π ε).mapRule r ∈ S := hr
    have := hU (autSubst π.symm (invEps π ε)) _ hmem
    rw [← mapRule_autAut] at this
    have hcomp : (autAut π.symm (invEps π ε)).mapRule ((autAut π ε).mapRule r) = r := by
      obtain ⟨pre, just, con⟩ := r
      simp [LogAut.mapRule, autAut, autFormEquiv, autForm_symm_autForm]
    rwa [hcomp] at this
  · intro hr
    show (autAut π ε).mapRule r ∈ S
    rw [mapRule_autAut]
    exact hU _ r hr

/-! ## Symmetry -/

/-- **The tautological theory is symmetric.**  Flip the atoms where the two
valuations disagree; no permutation is needed.  Note that the flip has
arbitrary support, which is why `Aut(L)` must not be defined as the group
*generated by* single-atom negations. -/
theorem symmetricUnder_taut : SymmetricUnder (AutL A C) (∅ : Set (CForm A C)) := by
  intro M N _ _
  refine ⟨autAut (Equiv.refl A) (fun a => xor (M.atom a) (N.atom a)),
    ⟨Equiv.refl A, _, rfl⟩, ?_⟩
  funext a
  show xor (invEps (Equiv.refl A) (fun a => xor (M.atom a) (N.atom a)) a)
      (M.atom ((Equiv.refl A).symm a)) = N.atom a
  simp only [invEps, Equiv.refl_symm, Equiv.refl_apply]
  cases M.atom a <;> cases N.atom a <;> rfl

/-- Every atom automorphism preserves the tautological consequences. -/
theorem autAut_pre_Cn_empty (π : A ≃ A) (ε : A → Bool) :
    (autAut π ε : LogAut A C).pre (Cn (∅ : Set (CForm A C)))
      = Cn (∅ : Set (CForm A C)) := by
  have h : (autAut π ε : LogAut A C).pre (∅ : Set (CForm A C)) = ∅ :=
    Set.preimage_empty
  rw [← LogAut.Cn_pre, h]

/-! ## The trichotomy -/

variable {T : Set (CForm A C)} {S : Set (Rule A C)} {E : Set (CForm A C)}

theorem Cn_subset_extension (hE : IsExtension T S E) : Cn T ⊆ E := by
  rw [hE]
  intro p hp
  exact Set.mem_iUnion.mpr ⟨0, hp⟩

/-- **The trichotomy, in contrapositive form.**  If the schema is invariant
under a group that is transitive on the models of `T`, and the extension is
unique and consistent, then nothing new arrives at the base language. -/
theorem trichotomy_core {G : Set (LogAut A C)}
    (hGT : ∀ g ∈ G, g.pre (Cn T) = Cn T)
    (hGS : ∀ g ∈ G, g.preRules S = S)
    (hGB : ∀ g ∈ G, ∀ p : CForm A C, IsBase p → IsBase (g.form p))
    (hsym : SymmetricUnder G T)
    (hE : IsExtension T S E) (hcon : Consistent E)
    (huniq : ∀ E', IsExtension T S E' → Consistent E' → E' = E) :
    ∀ φ : CForm A C, IsBase φ → φ ∈ E → φ ∈ Cn T := by
  intro φ hφ hmemE
  by_contra hnot
  simp only [Cn, Set.mem_setOf_eq] at hnot
  push Not at hnot
  obtain ⟨M, hMT, hMφ⟩ := hnot
  obtain ⟨v, hv⟩ := id hcon
  -- The model of `E` is in particular a model of `T`.
  have hvT : Models T v := fun q hq => hv q (Cn_subset_extension hE (subset_Cn T hq))
  -- Move the counter-model onto it.
  obtain ⟨g, hgG, hatom⟩ := hsym M v hMT hvT
  -- Step 1: the extension is invariant.
  have hinv : g.pre E = E :=
    huniq _ (LogAut.isExtension_pre g (hGT g hgG) (hGS g hgG) hE)
      (LogAut.consistent_pre g hcon)
  have hgφ : g.form φ ∈ E := by
    have : φ ∈ g.pre E := by rw [hinv]; exact hmemE
    exact this
  -- Step 2: but `g φ` is false in that model.
  have hfalse : eval (g.val.symm M) (g.form φ) = false := by
    rw [g.eval_form, g.val.apply_symm_apply]
    simpa using hMφ
  have hbase : IsBase (g.form φ) := hGB g hgG φ hφ
  have : eval v (g.form φ) = false := by
    rw [eval_base_congr hatom.symm _ hbase]
    exact hfalse
  rw [hv _ hgφ] at this
  exact Bool.noConfusion this

/-- **The trichotomy.**  At least one of the three disjuncts holds:
conservativity, failure of uniqueness, or failure of uniformity. -/
theorem trichotomy {G : Set (LogAut A C)}
    (hGT : ∀ g ∈ G, g.pre (Cn T) = Cn T)
    (hGB : ∀ g ∈ G, ∀ p : CForm A C, IsBase p → IsBase (g.form p))
    (hsym : SymmetricUnder G T)
    (hE : IsExtension T S E) (hcon : Consistent E) :
    (∀ φ : CForm A C, IsBase φ → φ ∈ E → φ ∈ Cn T)
    ∨ (¬ ∀ E', IsExtension T S E' → Consistent E' → E' = E)
    ∨ (¬ ∀ g ∈ G, g.preRules S = S) := by
  by_cases hP : ∀ g ∈ G, g.preRules S = S
  · by_cases hU : ∀ E', IsExtension T S E' → Consistent E' → E' = E
    · exact Or.inl (trichotomy_core hGT hP hGB hsym hE hcon hU)
    · exact Or.inr (Or.inl hU)
  · exact Or.inr (Or.inr hP)

/-- The trichotomy over the tautological base theory, which is the case
McCarthy's question is about: the base is assumed to contribute nothing, so any
novelty would have to come from the tower. -/
theorem trichotomy_taut {S : Set (Rule A C)} {E : Set (CForm A C)}
    (hE : IsExtension (∅ : Set (CForm A C)) S E) (hcon : Consistent E) :
    (∀ φ : CForm A C, IsBase φ → φ ∈ E → φ ∈ Cn (∅ : Set (CForm A C)))
    ∨ (¬ ∀ E', IsExtension (∅ : Set (CForm A C)) S E' → Consistent E' → E' = E)
    ∨ (¬ ∀ g ∈ AutL A C, g.preRules S = S) := by
  refine trichotomy ?_ ?_ symmetricUnder_taut hE hcon
  · rintro g ⟨π, ε, rfl⟩
    exact autAut_pre_Cn_empty π ε
  · rintro g ⟨π, ε, rfl⟩ p hp
    exact autForm_isBase π ε p hp

/-! ## Corner (C) is occupied

The copy schema is proposition-uniform, so `Aut(L)` preserves it, and it is
monotone, so its consistent extension is unique.  The trichotomy therefore
places it in (C), and that is proved rather than assumed: nothing new arrives
at the base language. -/

section Copy

theorem copyRules_propUniform : PropUniformRules (copyRules A C) := by
  rintro s r ⟨c, p, rfl⟩
  exact ⟨c, subst s p, rfl⟩

/-- The copy schema is invariant under the whole automorphism group. -/
theorem copyRules_autInvariant :
    ∀ g ∈ AutL A C, g.preRules (copyRules A C) = copyRules A C := by
  rintro g ⟨π, ε, rfl⟩
  exact preRules_autAut copyRules_propUniform π ε

/-- **The copy schema is conservative over the tautological theory**, by the
trichotomy rather than by direct computation.  This is the corner the paper
assigns it. -/
theorem copy_conservative (atomv : A → Bool) :
    ∀ φ : CForm A C, IsBase φ →
      φ ∈ (⋃ i, stage (∅ : Set (CForm A C)) (copyRules A C) ∅ i) →
      φ ∈ Cn (∅ : Set (CForm A C)) := by
  have hc : Consistent (⋃ i, stage (∅ : Set (CForm A C)) (copyRules A C) ∅ i) := by
    refine ⟨canonVal atomv, ?_⟩
    intro q hq
    obtain ⟨i, hi⟩ := Set.mem_iUnion.mp hq
    exact canonVal_models_stage atomv i q hi
  have hE := isExtension_monotone (T := (∅ : Set (CForm A C))) copyRules_monotone hc
  refine trichotomy_core (G := AutL A C) ?_ copyRules_autInvariant ?_
    symmetricUnder_taut hE hc
    (fun E' hE' hcE' => monotone_unique copyRules_monotone hE hc hE' hcE')
  · rintro g ⟨π, ε, rfl⟩
    exact autAut_pre_Cn_empty π ε
  · rintro g ⟨π, ε, rfl⟩ p hp
    exact autForm_isBase π ε p hp

end Copy

section Verification


end Verification





/-! ## Consequents -/

/-- The consequents of a schema, as a set of formulas. -/
def consequents (S : Set (Rule A C)) : Set (CForm A C) := {γ | ∃ r ∈ S, r.conseq = γ}

theorem fired_subset_consequents (S : Set (Rule A C)) (E X : Set (CForm A C)) :
    fired S E X ⊆ consequents S := by
  rintro γ ⟨r, hr, hc, _, _⟩
  exact ⟨r, hr, hc⟩

/-- Proposition-uniformity of a schema gives proposition-uniformity of its
consequents, which is the form the monotone dichotomy wants. -/
theorem consequents_propUniform {S : Set (Rule A C)} (hS : PropUniformRules S) :
    PropUniform (consequents S) := by
  rintro s γ ⟨r, hr, rfl⟩
  exact ⟨substRule s r, hS s r hr, rfl⟩

/-! ## The bridge

Only one inclusion is available, and only one is needed. -/

/-- Every stage of the construction lies inside `Cn (T ∪ consequents)`.  No
hypothesis on the schema is required. -/
theorem stage_subset_Cn_consequents (T : Set (CForm A C)) (S : Set (Rule A C))
    (E : Set (CForm A C)) : ∀ i, stage T S E i ⊆ Cn (T ∪ consequents S) := by
  intro i
  induction i with
  | zero => exact Cn_mono Set.subset_union_left
  | succ i ih =>
    intro p hp
    rcases hp with hp | hp
    · have h : p ∈ Cn (Cn (T ∪ consequents S)) := Cn_mono ih hp
      rwa [Cn_idem] at h
    · exact subset_Cn _ (Or.inr (fired_subset_consequents S E _ hp))

/-- Hence so does the extension. -/
theorem extension_subset_Cn_consequents {T : Set (CForm A C)} {S : Set (Rule A C)}
    {E : Set (CForm A C)} (hE : IsExtension T S E) : E ⊆ Cn (T ∪ consequents S) := by
  intro p hp
  rw [hE] at hp
  obtain ⟨i, hi⟩ := Set.mem_iUnion.mp hp
  exact stage_subset_Cn_consequents T S E i hi

/-- **The reverse inclusion fails.**  A monotone rule whose prerequisite is
never derived never fires, so its consequent need not reach the extension.
With the tautological base and the single rule `a : ⊤ / a`, the extension is
`Cn ∅` while `Cn (∅ ∪ {a})` contains `a`.

This is why the identity asserted in the paper's definition of an extension
needs restricting to prerequisite-free schemas. -/
theorem extension_ne_Cn_consequents (a : A) :
    ∃ (S : Set (Rule A C)) (E : Set (CForm A C)),
      Monotone S ∧ IsExtension (∅ : Set (CForm A C)) S E ∧
        E ≠ Cn ((∅ : Set (CForm A C)) ∪ consequents S) := by
  classical
  -- The valuation that falsifies every atom.
  let v : CVal A C := ⟨fun _ => false, fun _ _ => false⟩
  have hv : Models (∅ : Set (CForm A C)) v := fun _ hp => hp.elim
  have hnot : (CForm.lit a false : CForm A C) ∉ Cn (∅ : Set (CForm A C)) := by
    intro h
    have := h v hv
    simp [eval, v] at this
  refine ⟨{⟨CForm.lit a false, CForm.tru, CForm.lit a false⟩},
    Cn (∅ : Set (CForm A C)), ?_, ?_, ?_⟩
  · rintro r rfl
    rfl
  · -- No stage ever advances, because the prerequisite is never available.
    have hstage : ∀ i,
        stage (∅ : Set (CForm A C))
          ({⟨CForm.lit a false, CForm.tru, CForm.lit a false⟩} : Set (Rule A C))
          (Cn (∅ : Set (CForm A C))) i = Cn (∅ : Set (CForm A C)) := by
      intro i
      induction i with
      | zero => rfl
      | succ i ih =>
        show Cn (stage _ _ _ i) ∪ fired _ _ (stage _ _ _ i) = _
        rw [ih, Cn_idem]
        have hfired : fired ({⟨CForm.lit a false, CForm.tru, CForm.lit a false⟩} :
            Set (Rule A C)) (Cn (∅ : Set (CForm A C))) (Cn (∅ : Set (CForm A C))) = ∅ := by
          ext γ
          simp only [Set.mem_empty_iff_false, iff_false]
          rintro ⟨r, rfl, _, hpre, _⟩
          exact hnot hpre
        rw [hfired, Set.union_empty]
    show Cn (∅ : Set (CForm A C)) = ⋃ i, stage _ _ _ i
    simp [hstage, Set.iUnion_const]
  · intro hEq
    apply hnot
    rw [hEq]
    refine subset_Cn _ (Or.inr ?_)
    exact ⟨_, rfl, rfl⟩

/-! ## The audit property -/

/-- **Audit.**  If the update schema is proposition-uniform and the base theory
is context-free, the extension says exactly what the base theory says about the
world: no more, and no less.

Neither monotonicity of the schema nor symmetry of the base theory is required.
The second matters: a log is a specific claim about the world, so the
trichotomy's symmetry hypothesis would not be available here, and the monotone
dichotomy is the right instrument. -/
theorem audit {T : Set (CForm A C)} {S : Set (Rule A C)} {E : Set (CForm A C)}
    (hT : ∀ p ∈ T, IsBase p) (hS : PropUniformRules S)
    (hcon : Consistent (T ∪ consequents S)) (hE : IsExtension T S E) :
    ∀ φ : CForm A C, IsBase φ → (φ ∈ E ↔ φ ∈ Cn T) := by
  intro φ hφ
  constructor
  · intro hmem
    exact monotone_dichotomy hT (consequents_propUniform hS) hcon φ hφ
      (extension_subset_Cn_consequents hE hmem)
  · intro hmem
    exact Cn_subset_extension hE hmem

/-! ## Records -/

/-- The entries logged at or before revision `n`. -/
def logUpTo (Log : ℕ → Set (CForm A C)) (n : ℕ) : Set (CForm A C) :=
  {p | ∃ i ≤ n, p ∈ Log i}

theorem logUpTo_mono (Log : ℕ → Set (CForm A C)) {m n : ℕ} (h : m ≤ n) :
    logUpTo Log m ⊆ logUpTo Log n := by
  rintro p ⟨i, hi, hp⟩
  exact ⟨i, hi.trans h, hp⟩

theorem logUpTo_isBase {Log : ℕ → Set (CForm A C)}
    (hbase : ∀ n, ∀ p ∈ Log n, IsBase p) (n : ℕ) :
    ∀ p ∈ logUpTo Log n, IsBase p := by
  rintro p ⟨i, _, hp⟩
  exact hbase i p hp

section Record

variable {Log : ℕ → Set (CForm A C)} {S : Set (Rule A C)}
  {Ext : ℕ → Set (CForm A C)}
variable (hbase : ∀ n, ∀ p ∈ Log n, IsBase p)
variable (hS : PropUniformRules S)
variable (hcon : ∀ n, Consistent (logUpTo Log n ∪ consequents S))
variable (hExt : ∀ n, IsExtension (logUpTo Log n) S (Ext n))

include hbase hS hcon hExt

/-- **The record says exactly what was logged.** -/
theorem audit_at (n : ℕ) (φ : CForm A C) (hφ : IsBase φ) :
    φ ∈ Ext n ↔ φ ∈ Cn (logUpTo Log n) :=
  audit (logUpTo_isBase hbase n) hS (hcon n) (hExt n) φ hφ

/-- **Attribution.**  A base fact present at revision `n` and absent at
revision `m` is a consequence of the entries logged up to `n` and not of those
logged up to `m`.  Some entry in between is therefore necessary for it: there
are no facts in the record that no revision accounts for. -/
theorem attribution (m n : ℕ) (φ : CForm A C) (hφ : IsBase φ)
    (hnew : φ ∈ Ext n) (hold : φ ∉ Ext m) :
    φ ∈ Cn (logUpTo Log n) ∧ φ ∉ Cn (logUpTo Log m) := by
  refine ⟨(audit_at hbase hS hcon hExt n φ hφ).mp hnew, fun h => hold ?_⟩
  exact (audit_at hbase hS hcon hExt m φ hφ).mpr h

/-- **Nothing is lost silently.**  Base-language content only grows. -/
theorem no_silent_loss {m n : ℕ} (h : m ≤ n) (φ : CForm A C) (hφ : IsBase φ)
    (hmem : φ ∈ Ext m) : φ ∈ Ext n := by
  refine (audit_at hbase hS hcon hExt n φ hφ).mpr ?_
  exact Cn_mono (logUpTo_mono Log h) ((audit_at hbase hS hcon hExt m φ hφ).mp hmem)

end Record

section Verification


end Verification


end TranscendenceTower.UniformityPlatform

open TranscendenceTower.UniformityPlatform

theorem solution (A C : Type) :
    (∀ (T : Set (CForm A C)) (S : Set (Rule A C)) (E : Set (CForm A C)),
        (∀ p ∈ T, IsBase p) → PropUniformRules S →
        Consistent (T ∪ {γ | ∃ r ∈ S, r.conseq = γ}) →
        IsExtension T S E →
        ∀ φ : CForm A C, IsBase φ → (φ ∈ E ↔ φ ∈ Cn T))
    ∧ (∀ (Log : ℕ → Set (CForm A C)) (S : Set (Rule A C))
          (Ext : ℕ → Set (CForm A C)),
        (∀ n, ∀ p ∈ Log n, IsBase p) → PropUniformRules S →
        (∀ n, Consistent ({p | ∃ i ≤ n, p ∈ Log i} ∪ {γ | ∃ r ∈ S, r.conseq = γ})) →
        (∀ n, IsExtension {p | ∃ i ≤ n, p ∈ Log i} S (Ext n)) →
        ∀ (m n : ℕ) (φ : CForm A C), IsBase φ → φ ∈ Ext n → φ ∉ Ext m →
          φ ∈ Cn {p | ∃ i ≤ n, p ∈ Log i} ∧ φ ∉ Cn {p | ∃ i ≤ m, p ∈ Log i})
    ∧ (∀ (Log : ℕ → Set (CForm A C)) (S : Set (Rule A C))
          (Ext : ℕ → Set (CForm A C)),
        (∀ n, ∀ p ∈ Log n, IsBase p) → PropUniformRules S →
        (∀ n, Consistent ({p | ∃ i ≤ n, p ∈ Log i} ∪ {γ | ∃ r ∈ S, r.conseq = γ})) →
        (∀ n, IsExtension {p | ∃ i ≤ n, p ∈ Log i} S (Ext n)) →
        ∀ m n : ℕ, m ≤ n → ∀ φ : CForm A C, IsBase φ → φ ∈ Ext m → φ ∈ Ext n)
    ∧ (∀ a : A, ∃ (S : Set (Rule A C)) (E : Set (CForm A C)),
        Monotone S ∧ IsExtension (∅ : Set (CForm A C)) S E ∧
          E ≠ Cn ((∅ : Set (CForm A C)) ∪ {γ | ∃ r ∈ S, r.conseq = γ})) := by
  exact ⟨fun _ _ _ hT hS hcon hE => audit hT hS hcon hE,
         fun _ _ _ hb hS hc hE m n φ hφ h1 h2 => attribution hb hS hc hE m n φ hφ h1 h2,
         fun _ _ _ hb hS hc hE _ _ hmn φ hφ hm => no_silent_loss hb hS hc hE hmn φ hφ hm,
         fun a => extension_ne_Cn_consequents a⟩
