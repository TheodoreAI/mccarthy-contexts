/-
  Corollary 1 of "Consistency of a Stratified Formalization of McCarthy's
  Transcendence Tower": for every ordinal α, the tower Γ_α is consistent.

  McCarthy explicitly considers, and sets aside, continuing the transcendence
  process transfinitely. The paper records the extension as a corollary, saying
  "no new idea is needed; the induction is simply carried out on ordinals rather
  than natural numbers."  That is true of the mathematics but NOT of the
  formalization, where the limit stages have to be handled explicitly -- so this
  is a separate development rather than a reindexing of the finite one.

  Design notes.

  * The finite file indexes the syntax by a type family `Atom : ℕ → Type`.
    That does not transpose to ordinals: it would need type-valued transfinite
    recursion with an explicit colimit at limit stages.  Instead we use one
    untyped syntax `TForm` together with an inductive *membership predicate*
    `InLang α p` ("p ∈ L_α").  Successor and limit stages are then handled by
    the same generation rules, with no case split at all.

  * `IsLimitOrd` is defined here rather than imported, as
    `0 < lam ∧ ∀ β < lam, ∃ γ, β < γ ∧ γ < lam`.  This is the standard
    characterisation, and it keeps the development independent of Mathlib's
    (repeatedly renamed) successor-ordinal API: nothing below uses `Order.succ`.
-/

import Mathlib.SetTheory.Ordinal.Arithmetic

set_option autoImplicit false

namespace TranscendenceTower.Transfinite

open Ordinal

/-! ## Syntax -/

/-- Untyped syntax for the transfinite tower: base atoms `P₀`, an `istβ`
operator for each ordinal `β`, and the classical connectives.  Stratification is
imposed separately by `InLang`, not by the type. -/
inductive TForm : Type 1 where
  | atom : Nat → TForm
  | ist  : Ordinal → TForm → TForm
  | neg  : TForm → TForm
  | conj : TForm → TForm → TForm
  | disj : TForm → TForm → TForm
  | impl : TForm → TForm → TForm

namespace TForm

/-- The biconditional. -/
def iff (p q : TForm) : TForm := conj (impl p q) (impl q p)

end TForm

/-! ## Definition 1, transfinite form -/

/-- `InLang α p` says `p ∈ L_α`.

The `ist` rule is the whole content: `istβ(φ)` enters `L_α` only for `β < α` and
`φ ∈ L_β`, so `istβ` can never be applied to anything mentioning `istβ` itself.
This is Tarski's stratification, now indexed by ordinals; successor and limit
stages need no separate clauses. -/
inductive InLang : Ordinal → TForm → Prop where
  | atom {α : Ordinal} (k : Nat) : InLang α (TForm.atom k)
  | ist  {α β : Ordinal} {p : TForm} :
      β < α → InLang β p → InLang α (TForm.ist β p)
  | neg  {α : Ordinal} {p : TForm} : InLang α p → InLang α (TForm.neg p)
  | conj {α : Ordinal} {p q : TForm} :
      InLang α p → InLang α q → InLang α (TForm.conj p q)
  | disj {α : Ordinal} {p q : TForm} :
      InLang α p → InLang α q → InLang α (TForm.disj p q)
  | impl {α : Ordinal} {p q : TForm} :
      InLang α p → InLang α q → InLang α (TForm.impl p q)

/-- The languages form a chain: `β ≤ α → L_β ⊆ L_α`.  This is the cumulativity
that makes the tower a chain, here proved once for all ordinals. -/
theorem InLang.mono {β α : Ordinal} (h : β ≤ α) {p : TForm} :
    InLang β p → InLang α p := by
  intro hp
  induction hp generalizing α with
  | atom k => exact InLang.atom k
  | ist hlt _ ih => exact InLang.ist (lt_of_lt_of_le hlt h) (ih le_rfl)
  | neg _ ih => exact InLang.neg (ih h)
  | conj _ _ ihp ihq => exact InLang.conj (ihp h) (ihq h)
  | disj _ _ ihp ihq => exact InLang.disj (ihp h) (ihq h)
  | impl _ _ ihp ihq => exact InLang.impl (ihp h) (ihq h)

/-! ## Limit stages -/

/-- A limit ordinal: nonzero, with no greatest element below it.  Stated
directly so that nothing here depends on Mathlib's successor API. -/
def IsLimitOrd (lam : Ordinal) : Prop :=
  0 < lam ∧ ∀ β, β < lam → ∃ γ, β < γ ∧ γ < lam

/-- **The limit stage is the union of the earlier stages**: for a limit `lam`,
`L_lam = ⋃_{β < lam} L_β`.

This is the one place where the transfinite tower could have gone wrong -- the
paper's `M_lam = ⋃_{β<lam} M_β` is only well defined because every formula of
the limit language already appears at some earlier stage.  It does. -/
theorem InLang.exists_lt_of_limit {lam : Ordinal} (hlim : IsLimitOrd lam)
    {p : TForm} (hp : InLang lam p) : ∃ β, β < lam ∧ InLang β p := by
  induction hp with
  | atom k => exact ⟨0, hlim.1, InLang.atom k⟩
  | @ist _ β p hlt hpβ _ =>
      -- `istβ p` needs a stage strictly above β; a limit supplies one.
      obtain ⟨γ, hβγ, hγlam⟩ := hlim.2 β hlt
      exact ⟨γ, hγlam, InLang.ist hβγ hpβ⟩
  -- `induction` reverts `hlim` (it mentions the index `lam`), so each induction
  -- hypothesis takes the limit hypothesis as an argument; feed it back in.
  | neg _ ih =>
      obtain ⟨β, hβ, hp⟩ := ih hlim
      exact ⟨β, hβ, InLang.neg hp⟩
  | conj _ _ ihp ihq =>
      obtain ⟨β₁, hβ₁, hp⟩ := ihp hlim
      obtain ⟨β₂, hβ₂, hq⟩ := ihq hlim
      exact ⟨max β₁ β₂, max_lt hβ₁ hβ₂,
        InLang.conj (hp.mono (le_max_left _ _)) (hq.mono (le_max_right _ _))⟩
  | disj _ _ ihp ihq =>
      obtain ⟨β₁, hβ₁, hp⟩ := ihp hlim
      obtain ⟨β₂, hβ₂, hq⟩ := ihq hlim
      exact ⟨max β₁ β₂, max_lt hβ₁ hβ₂,
        InLang.disj (hp.mono (le_max_left _ _)) (hq.mono (le_max_right _ _))⟩
  | impl _ _ ihp ihq =>
      obtain ⟨β₁, hβ₁, hp⟩ := ihp hlim
      obtain ⟨β₂, hβ₂, hq⟩ := ihq hlim
      exact ⟨max β₁ β₂, max_lt hβ₁ hβ₂,
        InLang.impl (hp.mono (le_max_left _ _)) (hq.mono (le_max_right _ _))⟩

/-! ### `IsLimitOrd` is the right notion, and it is not vacuous

`IsLimitOrd` is defined above rather than imported, so two things need
checking: that it agrees with the standard notion, and that something actually
satisfies it -- otherwise `exists_lt_of_limit` would be vacuously true and would
establish nothing about limit stages. -/

/-- `IsLimitOrd` coincides with the usual "nonzero and closed under successor"
definition of a limit ordinal. -/
theorem isLimitOrd_iff_succ_lt (lam : Ordinal) :
    IsLimitOrd lam ↔ (0 < lam ∧ ∀ β, β < lam → Order.succ β < lam) := by
  constructor
  · rintro ⟨hpos, h⟩
    refine ⟨hpos, fun β hβ => ?_⟩
    obtain ⟨γ, hβγ, hγ⟩ := h β hβ
    exact lt_of_le_of_lt (Order.succ_le_of_lt hβγ) hγ
  · rintro ⟨hpos, h⟩
    exact ⟨hpos, fun β hβ => ⟨Order.succ β, Order.lt_succ β, h β hβ⟩⟩

/-- **Non-vacuity**: `ω` is a limit in this sense, so the limit-stage theorem
above has content.  (McCarthy's own tower `c₀, c₋₁, c₋₂, …` reaches exactly
`ω`; going beyond it is the generality he raises and sets aside.) -/
theorem isLimitOrd_omega0 : IsLimitOrd Ordinal.omega0 :=
  ⟨Ordinal.omega0_pos, fun _ hβ =>
    ⟨Order.succ _, Order.lt_succ _, Ordinal.isSuccLimit_omega0.succ_lt hβ⟩⟩

/-- The converse inclusion, for completeness: everything from an earlier stage
is in the limit stage.  With the previous theorem this gives the set equality
`L_lam = ⋃_{β<lam} L_β`. -/
theorem InLang.of_lt {lam β : Ordinal} (h : β < lam) {p : TForm}
    (hp : InLang β p) : InLang lam p :=
  hp.mono (le_of_lt h)

/-! ## Definition 2 and the model, transfinite form -/

/-- The instance `istβ(φ) ↔ φ` of the transcendence schema. -/
def schema (β : Ordinal) (p : TForm) : TForm :=
  TForm.iff (TForm.ist β p) p

/-- `Γ_α`: the schema extended to stage `α`. -/
def Gamma (α : Ordinal) : Set TForm :=
  {q | ∃ β p, β < α ∧ InLang β p ∧ q = schema β p}

/-- The tower valuation, parameterised by an arbitrary assignment `v0` to the
base atoms `P₀` (the paper takes "any truth assignment to `P₀`", so we do not
fix one).

Where the finite development built a chain `M₀ ⊆ M₁ ⊆ ⋯` and took a direct
limit, here the whole chain is realised at once by a single structural
recursion: the clause `val (istβ p) = val p` is the defining clause of every
successor stage, and because it is a single function, the coherence that makes
the limit union well defined holds by construction. -/
def val (v0 : Nat → Bool) : TForm → Bool
  | TForm.atom k   => v0 k
  | TForm.ist _ p  => val v0 p
  | TForm.neg p    => !(val v0 p)
  | TForm.conj p q => (val v0 p) && (val v0 q)
  | TForm.disj p q => (val v0 p) || (val v0 q)
  | TForm.impl p q => !(val v0 p) || (val v0 q)

/-- A biconditional is true exactly when its sides agree. -/
theorem val_iff (v0 : Nat → Bool) (p q : TForm) :
    val v0 (TForm.iff p q) = true ↔ val v0 p = val v0 q := by
  simp only [TForm.iff, val]
  cases hp : val v0 p <;> cases hq : val v0 q <;> simp

/-- Every instance of the schema is true in the tower model, at every ordinal
stage.  This is the transfinite analogue of `schema_true`. -/
theorem val_schema (v0 : Nat → Bool) (β : Ordinal) (p : TForm) :
    val v0 (schema β p) = true := by
  rw [schema, val_iff]
  rfl

/-- Schema instances live where they should: `istβ(φ) ↔ φ` belongs to `L_α`
whenever `β < α` and `φ ∈ L_β`. -/
theorem schema_mem {α β : Ordinal} (h : β < α) {p : TForm} (hp : InLang β p) :
    InLang α (schema β p) := by
  have hip : InLang α (TForm.ist β p) := InLang.ist h hp
  have hpα : InLang α p := hp.mono (le_of_lt h)
  exact InLang.conj (InLang.impl hip hpα) (InLang.impl hpα hip)

/-- `Γ_α` really is a set of `L_α`-sentences. -/
theorem Gamma_subset_Lang (α : Ordinal) :
    ∀ q ∈ Gamma α, InLang α q := by
  rintro q ⟨β, p, hβ, hp, rfl⟩
  exact schema_mem hβ hp

/-! ## Corollary 1 -/

/-- **Corollary 1.** For every ordinal `α`, the tower `Γ_α` -- the transcendence
schema extended to stage `α` -- is satisfiable, hence consistent.

This matches the generality McCarthy gestures at when he raises, and sets aside,
continuing the transcendence process transfinitely. -/
theorem Gamma_satisfiable (α : Ordinal) :
    ∃ v : TForm → Bool, ∀ q ∈ Gamma α, v q = true := by
  refine ⟨val (fun _ => false), ?_⟩
  rintro q ⟨β, p, _, _, rfl⟩
  exact val_schema _ β p

/-- The stronger form: *every* choice of base assignment already works, so
consistency does not depend on the valuation chosen for `P₀`. -/
theorem Gamma_satisfiable_of_base (α : Ordinal) (v0 : Nat → Bool) :
    ∀ q ∈ Gamma α, val v0 q = true := by
  rintro q ⟨β, p, _, _, rfl⟩
  exact val_schema v0 β p

/-! ## Verification -/

section Verification

/-- Corollary 1 restated inline, with the schema unfolded. -/
example : ∀ (α : Ordinal), ∃ v : TForm → Bool,
    ∀ (β : Ordinal) (p : TForm), β < α → InLang β p →
      v (TForm.iff (TForm.ist β p) p) = true := by
  intro α
  refine ⟨val (fun _ => false), ?_⟩
  intro β p _ _
  exact val_schema _ β p

/-- The limit-stage union restated inline. -/
example : ∀ (lam : Ordinal), IsLimitOrd lam → ∀ (p : TForm),
    InLang lam p → ∃ β, β < lam ∧ InLang β p :=
  fun _ h _ hp => InLang.exists_lt_of_limit h hp

/-- Non-vacuity restated inline: there really is a limit stage, and at it the
union property holds. -/
example : ∃ lam : Ordinal, IsLimitOrd lam ∧
    ∀ p : TForm, InLang lam p → ∃ β, β < lam ∧ InLang β p :=
  ⟨Ordinal.omega0, isLimitOrd_omega0,
   fun _ hp => InLang.exists_lt_of_limit isLimitOrd_omega0 hp⟩

#print axioms InLang.mono
#print axioms InLang.exists_lt_of_limit
#print axioms isLimitOrd_iff_succ_lt
#print axioms isLimitOrd_omega0
#print axioms val_iff
#print axioms val_schema
#print axioms schema_mem
#print axioms Gamma_subset_Lang
#print axioms Gamma_satisfiable
#print axioms Gamma_satisfiable_of_base

end Verification

end TranscendenceTower.Transfinite
