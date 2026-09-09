/-
  The audit property: what a record can be made to say.

  A record is a sequence of revisions.  Each revision logs some entries in the
  base language, and an update schema carries material from one revision to the
  next.  The question an auditor asks is whether the record can come to contain
  a fact that no entry accounts for.

  The answer here is that it cannot, provided the update schema is
  proposition-uniform: the base-language content of the extension at revision
  `n` is exactly the consequences of the entries logged up to `n`.  Every new
  fact is attributable to a revision.

  Two things about the route.

  * The bridge one first reaches for — that the extension of a monotone schema
    is `Cn (T ∪ consequents)` — is FALSE, and `extension_ne_Cn_consequents` below
    exhibits a one-rule counterexample.  A monotone rule still has a
    prerequisite, and a rule whose prerequisite is never derived never fires,
    so its consequent need not be in the extension.  The paper states the
    identity in its definition of an extension; the claim needs restricting to
    prerequisite-free schemas.

  * The identity is not needed anyway.  Only one inclusion is, and it holds for
    every schema whatever: each stage of the Reiter construction sits inside
    `Cn (T ∪ consequents)`, so conservativity transfers down from the monotone
    dichotomy to the extension.  Neither monotonicity nor symmetry of the base
    theory is used, which matters here because a real log is the opposite of
    symmetric.
-/

import Development.Trichotomy

set_option autoImplicit false

namespace TranscendenceTower.Uniformity

variable {A C : Type}

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

#print axioms extension_subset_Cn_consequents
#print axioms extension_ne_Cn_consequents
#print axioms audit
#print axioms audit_at
#print axioms attribution
#print axioms no_silent_loss

end Verification

end TranscendenceTower.Uniformity
