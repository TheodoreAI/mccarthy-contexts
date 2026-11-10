/-
  On the Necessity of External Semantic Oracles in Autonomous Software
  Engineering Systems: A Meta-Theoretic Analysis via Context Logic, Tarski's
  Undefinability, and Relativized Computability.

  This module proves the paper's main results over concrete structures from
  Mathlib's computability library (`Nat.Partrec.Code`, `ComputablePred`) and
  the context-logic / Reiter-extension framework (`CForm A C`, `IsExtension`,
  `PropUniformRules`):

    1. Closure of Computable Verifiers & Bounded Test Harnesses (`Code.evaln`):
       Every bounded-step test assertion `(k, x, y)` is primitive recursive,
       hence computable; any finite pipeline `Os.foldl (fun b O => b && O c) (d₀ c)`
       of computable verifiers and sub-oracles is computable.

    2. Lemma 1 & Theorem 1 (Steps 1–2) — Rice Undecidability for Multi-Oracle
       Pipelines (`pipeline_rice_undecidable`):
       For any non-trivial semantic specification `Spec : Set Code`, every
       finite composition of computable sub-oracles fails on some program
       `c_star : Code` (either certifying an invalid program `c_star ∉ Spec`
       or rejecting a valid program `c_star ∈ Spec`).

    3. Lemma 2 — Syntactic Collapse of Closed Uniform Agent Loops
       (`closed_loop_syntactic_collapse`):
       For any context-free specification `Ax : Set (CForm A C)` and any
       Reiter extension `Ext` of a proposition-uniform rule schema `S`, the
       base-language content of `Ext` collapses to `Cn Ax`.

    4. Lemma 3 — Undecidability & Silent Semantic Drift in Closed Loops
       (`closed_loop_undecided_under_drift`):
       Whenever an operational requirement `G_star` holds in `c_reality`
       (`v_real`) but fails in a drifted model `v_drift` of `Ax`, the closed
       loop `Ext` can neither certify `G_star` nor certify `neg G_star`.

    5. Theorem 1 (Steps 3–4) — Necessity & Sufficiency of Non-Uniform External
       Oracle Grounding (`necessary_external_grounding`):
       No consistent proposition-uniform lifting set `LiftAx` can ever certify
       an unforced requirement `G_star ∉ Cn Ax` (`¬ PropUniform LiftAx`),
       whereas the external semantic oracle injection
       `LiftAx = {ist c_real G_star, ist c_real G_star → G_star}` is consistent
       with `Ax`, certifies `G_star`, and is necessarily non-uniform.
-/

import Development.Audit
import Mathlib.Computability.Halting

set_option autoImplicit false

namespace TranscendenceTower.Uniformity

open Computable
open Nat.Partrec (Code)

variable {A C : Type}

/-! ## 1. Closure of Computable Verifiers & Bounded Test Harnesses -/

/-- If two boolean predicates on program codes are computable, so is their
pointwise conjunction. -/
theorem computable_and {f g : Code → Bool} (hf : Computable f) (hg : Computable g) :
    Computable (fun c : Code => f c && g c) := by
  have h := Computable.cond hf hg (Computable.const false)
  refine h.of_eq fun c => ?_
  cases f c <;> rfl

/-- Internalizing any finite list of computable verification sub-oracles
`Os : List (Code → Bool)` into a computable base verifier `d₀ : Code → Bool`
yields a computable composite verifier. -/
theorem pipeline_foldl_computable (d₀ : Code → Bool) (Os : List (Code → Bool))
    (hd₀ : Computable d₀) (hOs : ∀ O ∈ Os, Computable O) :
    Computable (fun c : Code => Os.foldl (fun acc O => acc && O c) (d₀ c)) := by
  induction Os generalizing d₀ with
  | nil => exact hd₀
  | cons O Os ih =>
    have hO : Computable O := hOs O (by simp)
    have hRest : ∀ O' ∈ Os, Computable O' := fun O' hO' => hOs O' (by simp [hO'])
    exact ih (fun c => d₀ c && O c) (computable_and hd₀ hO) hRest

/-- Every bounded-step execution test `(k, x, y)` checking whether program `c`
halts within `k` steps on input `x` with output `y` (`Code.evaln k c x = some y`)
is computable (`Tier 3: Automated Test Harness`). -/
theorem bounded_test_computable (k x y : ℕ) :
    Computable (fun c : Code => decide (Code.evaln k c x = some y)) := by
  have h_in : Primrec (fun c : Code => ((k, c), x)) :=
    ((Primrec.const k).pair Primrec.id).pair (Primrec.const x)
  have h_evaln : Primrec (fun c : Code => Code.evaln k c x) :=
    Code.primrec_evaln.comp h_in
  have h_eq : PrimrecPred (fun c : Code => Code.evaln k c x = some y) :=
    Primrec.eq.comp h_evaln (Primrec.const (some y))
  exact h_eq.computablePred.decide

/-! ## 2. Rice Undecidability for Multi-Oracle Verification Pipelines -/

/-- **Lemma 1 & Theorem 1 (Steps 1–2): Multi-Oracle Rice Undecidability.**

Let `Spec : Set Code` be any non-trivial semantic property of programs in
`Nat.Partrec.Code`.  For any computable base verifier `d₀ : Code → Bool` and
any finite list of internalized computable sub-oracles `Os : List (Code → Bool)`
(such as static type checkers, compilers, and bounded test harnesses), there
exists a witness program `c_star : Code` on which the composite pipeline's
verdict disagrees with `Spec`. -/
theorem pipeline_rice_undecidable (Spec : Set Code)
    (hSem : ∀ c₁ c₂ : Code, Code.eval c₁ = Code.eval c₂ → (c₁ ∈ Spec ↔ c₂ ∈ Spec))
    (hNonTriv : (∃ c_yes : Code, c_yes ∈ Spec) ∧ (∃ c_no : Code, c_no ∉ Spec))
    (d₀ : Code → Bool) (Os : List (Code → Bool))
    (hd₀ : Computable d₀) (hOs : ∀ O ∈ Os, Computable O) :
    ∃ c_star : Code,
      (Os.foldl (fun acc O => acc && O c_star) (d₀ c_star) = true) ↔ c_star ∉ Spec := by
  classical
  by_contra hAll
  push Not at hAll
  have hComp : Computable (fun c : Code => Os.foldl (fun acc O => acc && O c) (d₀ c)) :=
    pipeline_foldl_computable d₀ Os hd₀ hOs
  have hPredPipe : ComputablePred (fun c : Code =>
      Os.foldl (fun acc O => acc && O c) (d₀ c) = true) := by
    refine Computable.computablePred ?_
    simpa using hComp
  have hEquiv : ∀ c : Code,
      (Os.foldl (fun acc O => acc && O c) (d₀ c) = true) ↔ c ∈ Spec := by
    intro c
    have hc := hAll c
    tauto
  have hPredSpec : ComputablePred (fun c : Code => c ∈ Spec) :=
    hPredPipe.of_eq hEquiv
  have hTriv : Spec = ∅ ∨ Spec = Set.univ :=
    (ComputablePred.rice₂ Spec hSem).mp hPredSpec
  rcases hNonTriv with ⟨⟨c_yes, hyes⟩, ⟨c_no, hno⟩⟩
  rcases hTriv with rfl | rfl
  · exact hyes
  · exact hno (Set.mem_univ c_no)

/-- Non-vacuity witness for `Spec`: the halting specification at input `0` is a
non-trivial semantic property of `Code`. -/
theorem halting_at_zero_semantic_nontrivial :
    (∀ c₁ c₂ : Code, Code.eval c₁ = Code.eval c₂ →
      ((Code.eval c₁ 0).Dom ↔ (Code.eval c₂ 0).Dom)) ∧
    (∃ c_yes : Code, (Code.eval c_yes 0).Dom) ∧
    (∃ c_no : Code, ¬ (Code.eval c_no 0).Dom) := by
  obtain ⟨c_yes, hc_yes⟩ := Nat.Partrec.Code.exists_code.1 Nat.Partrec.zero
  obtain ⟨c_no, hc_no⟩ := Nat.Partrec.Code.exists_code.1 Nat.Partrec.none
  refine ⟨fun _ _ hEq => by rw [hEq], ⟨c_yes, ?_⟩, ⟨c_no, ?_⟩⟩
  · rw [hc_yes]
    exact Part.some_dom 0
  · rw [hc_no]
    exact Part.not_none_dom

/-! ## 3. Context Logic: Base Evaluation, Collapse, and Semantic Drift -/

/-- Base formulas depend only on the atomic valuation `v.atom` and are
completely independent of the modal context assignment `v.ist`. -/
theorem eval_eq_of_atom_eq {v w : CVal A C} (hAtom : v.atom = w.atom) :
    ∀ p : CForm A C, IsBase p → eval v p = eval w p := by
  intro p
  induction p with
  | lit a b =>
    intro _
    simp [eval, hAtom]
  | fls =>
    intro _
    rfl
  | impl p q ihp ihq =>
    intro hb
    simp [eval, ihp hb.1, ihq hb.2]
  | ist c p _ =>
    intro hb
    exact hb.elim

/-- **Lemma 2 (Closed-Loop Collapse to Internal Consequence).**

In any closed verification architecture governed by a proposition-uniform rule
schema `S : Set (Rule A C)` over a context-free specification `Ax`, every
Reiter extension `Ext` (`IsExtension Ax S Ext`) with consistent consequents
collapses on base sentences to `Cn Ax`. -/
theorem closed_loop_syntactic_collapse
    {Ax : Set (CForm A C)} {S : Set (Rule A C)} {Ext : Set (CForm A C)}
    (hAx : ∀ p ∈ Ax, IsBase p) (hS : PropUniformRules S)
    (hcon : Consistent (Ax ∪ consequents S)) (hExt : IsExtension Ax S Ext) :
    ∀ φ : CForm A C, IsBase φ → (φ ∈ Ext ↔ φ ∈ Cn Ax) :=
  audit hAx hS hcon hExt

/-- **Lemma 3 (Undecidability & Silent Semantic Drift in Closed Agent Loops).**

Let `G_star` be a base-language requirement that holds in the target operational
reality `v_real` (`Models Ax v_real ∧ eval v_real G_star = true`), while a
drifted model `v_drift` also satisfies the internal specification `Ax`
(`Models Ax v_drift`) but falsifies `G_star` (`eval v_drift G_star = false`).
Then `G_star` is undecidable in every proposition-uniform Reiter extension
`Ext`: neither `G_star` nor `neg G_star` belongs to `Ext`. -/
theorem closed_loop_undecided_under_drift
    {Ax : Set (CForm A C)} {S : Set (Rule A C)} {Ext : Set (CForm A C)}
    {v_real v_drift : CVal A C} {G_star : CForm A C}
    (hAx : ∀ p ∈ Ax, IsBase p) (hS : PropUniformRules S)
    (hcon : Consistent (Ax ∪ consequents S)) (hExt : IsExtension Ax S Ext)
    (hG : IsBase G_star)
    (hRealMod : Models Ax v_real) (hRealTrue : eval v_real G_star = true)
    (hDriftMod : Models Ax v_drift) (hDriftFalse : eval v_drift G_star = false) :
    G_star ∉ Ext ∧ neg G_star ∉ Ext := by
  refine ⟨?_, ?_⟩
  · intro hIn
    have hCn : G_star ∈ Cn Ax :=
      (closed_loop_syntactic_collapse hAx hS hcon hExt G_star hG).mp hIn
    have hTrue : eval v_drift G_star = true := hCn v_drift hDriftMod
    rw [hDriftFalse] at hTrue
    exact Bool.noConfusion hTrue
  · intro hNegIn
    have hNegBase : IsBase (neg G_star) := isBase_neg hG
    have hCn : neg G_star ∈ Cn Ax :=
      (closed_loop_syntactic_collapse hAx hS hcon hExt (neg G_star) hNegBase).mp hNegIn
    have hNegTrue : eval v_real (neg G_star) = true := hCn v_real hRealMod
    rw [eval_neg, hRealTrue] at hNegTrue
    exact Bool.noConfusion hNegTrue

/-! ## 4. Main Result: Necessity & Sufficiency of Non-Uniform External Grounding -/

/-- **Theorem 1, Part A (Necessity of Non-Uniform External Grounding).**

If a base specification `G_star` is unprovable from `Ax` (`G_star ∉ Cn Ax`),
then no consistent proposition-uniform lifting axiom set `LiftAx` can ever
certify `G_star`.  Any sound grounding `LiftAx` must therefore be non-uniform:
it must inject domain-specific external semantic information rather than a
purely syntactic/uniform context rule. -/
theorem necessary_nonuniform_grounding
    {Ax LiftAx : Set (CForm A C)} {G_star : CForm A C}
    (hAx : ∀ p ∈ Ax, IsBase p) (hG : IsBase G_star)
    (hUnprov : G_star ∉ Cn Ax)
    (hCon : Consistent (Ax ∪ LiftAx))
    (hCert : G_star ∈ Cn (Ax ∪ LiftAx)) :
    ¬ PropUniform LiftAx := by
  intro hU
  exact hUnprov (monotone_dichotomy hAx hU hCon G_star hG hCert)

/-- The lifting axiom set injected by the external semantic oracle `R_nonalg`
in the supervisory meta-theory `M_ToE` for context `c_real` and specification
`G_star`: asserts `ist(c_real, G_star)` together with the lifting bridge
`ist(c_real, G_star) → G_star`. -/
def oracleGroundingSet (c_real : C) (G_star : CForm A C) : Set (CForm A C) :=
  {CForm.ist c_real G_star, CForm.impl (CForm.ist c_real G_star) G_star}

/-- Reality-grounded meta-valuation in `M_ToE`: retains `v_real.atom` on atoms
and interprets `ist c p` as `eval v_real p`. -/
def realityMetaVal (v_real : CVal A C) : CVal A C where
  atom := v_real.atom
  ist := fun _ p => eval v_real p

/-- **Theorem 1, Part B (Soundness, Sufficiency & Non-Uniformity of Supervisory
Meta-Theory Grounding).**

When `G_star` holds in the operational environment `v_real` (`Models Ax v_real`
and `eval v_real G_star = true`) but is unprovable from `Ax` alone
(`G_star ∉ Cn Ax`), the external oracle injection
`oracleGroundingSet c_real G_star`:
1. is **consistent** with `Ax`,
2. **certifies** `G_star` (`G_star ∈ Cn (Ax ∪ oracleGroundingSet c_real G_star)`), and
3. is **provably non-uniform** (`¬ PropUniform (oracleGroundingSet c_real G_star)`). -/
theorem external_oracle_grounding_sufficient
    {Ax : Set (CForm A C)} {v_real : CVal A C}
    (c_real : C) {G_star : CForm A C}
    (hAx : ∀ p ∈ Ax, IsBase p) (hG : IsBase G_star)
    (hRealMod : Models Ax v_real) (hRealTrue : eval v_real G_star = true)
    (hUnprov : G_star ∉ Cn Ax) :
    Consistent (Ax ∪ oracleGroundingSet c_real G_star) ∧
    G_star ∈ Cn (Ax ∪ oracleGroundingSet c_real G_star) ∧
    ¬ PropUniform (oracleGroundingSet c_real G_star) := by
  have hCon : Consistent (Ax ∪ oracleGroundingSet c_real G_star) := by
    refine ⟨realityMetaVal v_real, fun q hq => ?_⟩
    rcases hq with hq | hq
    · rw [eval_eq_of_atom_eq (v := realityMetaVal v_real) (w := v_real) rfl q (hAx q hq)]
      exact hRealMod q hq
    · rcases hq with rfl | hq
      · exact hRealTrue
      · rw [Set.mem_singleton_iff] at hq
        subst hq
        have hBaseEq : eval (realityMetaVal v_real) G_star = eval v_real G_star :=
          eval_eq_of_atom_eq (v := realityMetaVal v_real) (w := v_real) rfl G_star hG
        show (!(eval (realityMetaVal v_real) (CForm.ist c_real G_star)) ||
          eval (realityMetaVal v_real) G_star) = true
        rw [hBaseEq, hRealTrue, Bool.or_true]
  have hCert : G_star ∈ Cn (Ax ∪ oracleGroundingSet c_real G_star) := by
    intro v hv
    have hIst : eval v (CForm.ist c_real G_star) = true :=
      hv (CForm.ist c_real G_star) (Or.inr (Or.inl rfl))
    have hImp : eval v (CForm.impl (CForm.ist c_real G_star) G_star) = true :=
      hv (CForm.impl (CForm.ist c_real G_star) G_star) (Or.inr (Or.inr rfl))
    change (!(eval v (CForm.ist c_real G_star)) || eval v G_star) = true at hImp
    rw [hIst] at hImp
    exact hImp
  refine ⟨hCon, hCert, ?_⟩
  exact necessary_nonuniform_grounding hAx hG hUnprov hCon hCert

/-! ## 5. Combined Headline Theorem & Non-Vacuity Audit -/

/-- **Theorem of Necessary External Grounding (Full Synthesis).** -/
theorem necessary_external_grounding (A C : Type) :
    -- (1) Multi-oracle verification pipelines are computable and subject to Rice's Theorem
    (∀ (Spec : Set Code),
      (∀ c₁ c₂ : Code, Code.eval c₁ = Code.eval c₂ → (c₁ ∈ Spec ↔ c₂ ∈ Spec)) →
      ((∃ c_yes : Code, c_yes ∈ Spec) ∧ (∃ c_no : Code, c_no ∉ Spec)) →
      ∀ (d₀ : Code → Bool) (Os : List (Code → Bool)),
        Computable d₀ → (∀ O ∈ Os, Computable O) →
        ∃ c_star : Code,
          (Os.foldl (fun acc O => acc && O c_star) (d₀ c_star) = true) ↔ c_star ∉ Spec) ∧
    -- (2) Every bounded-step execution test (k, x, y) is a computable sub-oracle
    (∀ k x y : ℕ, Computable (fun c : Code => decide (Code.evaln k c x = some y))) ∧
    -- (3) Closed proposition-uniform agent loops cannot decide drifted specifications
    (∀ (Ax : Set (CForm A C)) (S : Set (Rule A C)) (Ext : Set (CForm A C))
       (v_real v_drift : CVal A C) (G_star : CForm A C),
      (∀ p ∈ Ax, IsBase p) → PropUniformRules S →
      Consistent (Ax ∪ {γ | ∃ r ∈ S, r.conseq = γ}) →
      IsExtension Ax S Ext → IsBase G_star →
      Models Ax v_real → eval v_real G_star = true →
      Models Ax v_drift → eval v_drift G_star = false →
      G_star ∉ Ext ∧ neg G_star ∉ Ext) ∧
    -- (4) External oracle injection in M_ToE is consistent, certifies G_star,
    --     and is necessarily non-uniform
    (∀ (Ax : Set (CForm A C)) (v_real : CVal A C) (c_real : C) (G_star : CForm A C),
      (∀ p ∈ Ax, IsBase p) → IsBase G_star →
      Models Ax v_real → eval v_real G_star = true → G_star ∉ Cn Ax →
      let LiftAx : Set (CForm A C) :=
        {CForm.ist c_real G_star, CForm.impl (CForm.ist c_real G_star) G_star}
      Consistent (Ax ∪ LiftAx) ∧ G_star ∈ Cn (Ax ∪ LiftAx) ∧ ¬ PropUniform LiftAx) := by
  refine ⟨pipeline_rice_undecidable, bounded_test_computable, ?_, ?_⟩
  · intro Ax S Ext v_real v_drift G_star hAx hS hcon hExt hG hRM hRT hDM hDF
    exact closed_loop_undecided_under_drift hAx hS hcon hExt hG hRM hRT hDM hDF
  · intro Ax v_real c_real G_star hAx hG hRM hRT hUnprov
    exact external_oracle_grounding_sufficient c_real hAx hG hRM hRT hUnprov

section Verification

/-- Non-vacuity witness: concrete instantiation of `pipeline_rice_undecidable`
on the halting problem at input `0` with a 1-step bounded test sub-oracle
`Code.evaln 1 c 0 = some 0`. -/
example :
    ∃ c_star : Code,
      ([fun c : Code => decide (Code.evaln 1 c 0 = some 0)].foldl
        (fun acc O => acc && O c_star) true = true) ↔
      ¬ (Code.eval c_star 0).Dom := by
  have ⟨hSem, hYes, hNo⟩ := halting_at_zero_semantic_nontrivial
  refine pipeline_rice_undecidable {c : Code | (Code.eval c 0).Dom}
    hSem ⟨hYes, hNo⟩ (fun _ => true)
    [fun c : Code => decide (Code.evaln 1 c 0 = some 0)]
    (Computable.const true) ?_
  intro O hO
  simp only [List.mem_singleton] at hO
  rw [hO]
  exact bounded_test_computable 1 0 0

/-- Non-vacuity witness: concrete instantiation of `external_oracle_grounding_sufficient`
with `A = Nat`, `C = Nat`, `Ax = ∅`, and `G_star = CForm.atom 0`. -/
example :
    let Ax : Set (CForm Nat Nat) := ∅
    let G_star : CForm Nat Nat := CForm.atom 0
    let LiftAx : Set (CForm Nat Nat) := oracleGroundingSet 0 G_star
    Consistent (Ax ∪ LiftAx) ∧ G_star ∈ Cn (Ax ∪ LiftAx) ∧ ¬ PropUniform LiftAx := by
  intro Ax G_star LiftAx
  let v_real : CVal Nat Nat := ⟨fun _ => true, fun _ _ => true⟩
  let v_drift : CVal Nat Nat := ⟨fun _ => false, fun _ _ => false⟩
  have hUnprov : G_star ∉ Cn Ax := by
    intro h
    have hFalse : eval v_drift G_star = true := h v_drift (fun _ hp => hp.elim)
    simp [G_star, CForm.atom, v_drift] at hFalse
  exact external_oracle_grounding_sufficient (v_real := v_real) 0
    (fun _ hp => hp.elim) trivial (fun _ hp => hp.elim) rfl hUnprov

#print axioms computable_and
#print axioms pipeline_foldl_computable
#print axioms bounded_test_computable
#print axioms pipeline_rice_undecidable
#print axioms halting_at_zero_semantic_nontrivial
#print axioms eval_eq_of_atom_eq
#print axioms closed_loop_syntactic_collapse
#print axioms closed_loop_undecided_under_drift
#print axioms necessary_nonuniform_grounding
#print axioms external_oracle_grounding_sufficient
#print axioms necessary_external_grounding

end Verification

end TranscendenceTower.Uniformity
