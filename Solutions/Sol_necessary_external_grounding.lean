import Definitions.Def_TranscendenceTowerContextUniformity
import Mathlib.Computability.Halting

set_option autoImplicit false
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

open Computable
open Nat.Partrec (Code)
open TranscendenceTower.UniformityPlatform

namespace TranscendenceTower.ExternalGroundingPlatform

variable {A C : Type}

/-! ## 1. Base language, substitution, and monotone dichotomy -/

theorem isBase_neg {p : CForm A C} (h : IsBase p) : IsBase (neg p) := by
  cases p with
  | lit a b => trivial
  | fls => exact ⟨trivial, trivial⟩
  | impl p q => exact ⟨h, trivial⟩
  | ist c p => exact h.elim

theorem eval_subst (v : CVal A C) (s : A → CForm A C) (p : CForm A C) :
    eval v (subst s p) = eval (pullback v s) p := by
  induction p with
  | lit a b => cases b <;> simp [subst, eval, pullback]
  | fls => rfl
  | impl p q ihp ihq => simp [eval, subst, ihp, ihq]
  | ist c p _ => rfl

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

theorem Cn_mono {X Y : Set (CForm A C)} (h : X ⊆ Y) : Cn X ⊆ Cn Y :=
  fun _ hp v hv => hp v fun q hq => hv q (h hq)

theorem Cn_idem (X : Set (CForm A C)) : Cn (Cn X) = Cn X :=
  Set.Subset.antisymm
    (fun _ hp v hv => hp v fun q hq => hq v hv)
    (subset_Cn _)

theorem eval_eq_of_atom_eq {v w : CVal A C} (hAtom : v.atom = w.atom) :
    ∀ p : CForm A C, IsBase p → eval v p = eval w p := by
  intro p
  induction p with
  | lit a b => intro _; simp [eval, hAtom]
  | fls => intro _; rfl
  | impl p q ihp ihq => intro hb; simp [eval, ihp hb.1, ihq hb.2]
  | ist c p _ => intro hb; exact hb.elim

/-! ## 2. Reiter extensions and closed-loop collapse -/

def consequents (S : Set (Rule A C)) : Set (CForm A C) :=
  {γ | ∃ r ∈ S, r.conseq = γ}

theorem fired_subset_consequents (S : Set (Rule A C)) (E X : Set (CForm A C)) :
    fired S E X ⊆ consequents S := by
  rintro γ ⟨r, hr, hc, _, _⟩
  exact ⟨r, hr, hc⟩

theorem consequents_propUniform {S : Set (Rule A C)} (hS : PropUniformRules S) :
    PropUniform (consequents S) := by
  rintro s γ ⟨r, hr, rfl⟩
  exact ⟨substRule s r, hS s r hr, rfl⟩

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

theorem extension_subset_Cn_consequents {T : Set (CForm A C)} {S : Set (Rule A C)}
    {E : Set (CForm A C)} (hE : IsExtension T S E) : E ⊆ Cn (T ∪ consequents S) := by
  intro p hp
  rw [hE] at hp
  obtain ⟨i, hi⟩ := Set.mem_iUnion.mp hp
  exact stage_subset_Cn_consequents T S E i hi

theorem Cn_subset_extension {T : Set (CForm A C)} {S : Set (Rule A C)}
    {E : Set (CForm A C)} (hE : IsExtension T S E) : Cn T ⊆ E := by
  intro p hp
  rw [hE]
  exact Set.mem_iUnion.mpr ⟨0, hp⟩

theorem closed_loop_syntactic_collapse
    {Ax : Set (CForm A C)} {S : Set (Rule A C)} {Ext : Set (CForm A C)}
    (hAx : ∀ p ∈ Ax, IsBase p) (hS : PropUniformRules S)
    (hcon : Consistent (Ax ∪ consequents S)) (hExt : IsExtension Ax S Ext) :
    ∀ φ : CForm A C, IsBase φ → (φ ∈ Ext ↔ φ ∈ Cn Ax) := by
  intro φ hφ
  constructor
  · intro hmem
    exact monotone_dichotomy hAx (consequents_propUniform hS) hcon φ hφ
      (extension_subset_Cn_consequents hExt hmem)
  · intro hmem
    exact Cn_subset_extension hExt hmem

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

def oracleGroundingSet (c_real : C) (G_star : CForm A C) : Set (CForm A C) :=
  {CForm.ist c_real G_star, CForm.impl (CForm.ist c_real G_star) G_star}

def realityMetaVal (v_real : CVal A C) : CVal A C where
  atom := v_real.atom
  ist := fun _ p => eval v_real p

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
  intro hU
  exact hUnprov (monotone_dichotomy hAx hU hCon G_star hG hCert)

/-! ## 3. Multi-Oracle Computability & Rice Undecidability -/

theorem computable_and {f g : Code → Bool} (hf : Computable f) (hg : Computable g) :
    Computable (fun c : Code => f c && g c) := by
  have h := Computable.cond hf hg (Computable.const false)
  refine h.of_eq fun c => ?_
  cases f c <;> rfl

theorem pipeline_foldl_computable (d₀ : Code → Bool) (Os : List (Code → Bool))
    (hd₀ : Computable d₀) (hOs : ∀ O ∈ Os, Computable O) :
    Computable (fun c : Code => Os.foldl (fun acc O => acc && O c) (d₀ c)) := by
  induction Os generalizing d₀ with
  | nil => exact hd₀
  | cons O Os ih =>
    have hO : Computable O := hOs O (by simp)
    have hRest : ∀ O' ∈ Os, Computable O' := fun O' hO' => hOs O' (by simp [hO'])
    exact ih (fun c => d₀ c && O c) (computable_and hd₀ hO) hRest

theorem bounded_test_computable (k x y : ℕ) :
    Computable (fun c : Code => decide (Code.evaln k c x = some y)) := by
  have h_in : Primrec (fun c : Code => ((k, c), x)) :=
    ((Primrec.const k).pair Primrec.id).pair (Primrec.const x)
  have h_evaln : Primrec (fun c : Code => Code.evaln k c x) :=
    Code.primrec_evaln.comp h_in
  have h_eq : PrimrecPred (fun c : Code => Code.evaln k c x = some y) :=
    Primrec.eq.comp h_evaln (Primrec.const (some y))
  exact h_eq.computablePred.decide

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

end TranscendenceTower.ExternalGroundingPlatform

open TranscendenceTower.ExternalGroundingPlatform

theorem solution (A C : Type) :
    (∀ (Spec : Set Code),
      (∀ c₁ c₂ : Code, Code.eval c₁ = Code.eval c₂ → (c₁ ∈ Spec ↔ c₂ ∈ Spec)) →
      ((∃ c_yes : Code, c_yes ∈ Spec) ∧ (∃ c_no : Code, c_no ∉ Spec)) →
      ∀ (d₀ : Code → Bool) (Os : List (Code → Bool)),
        Computable d₀ → (∀ O ∈ Os, Computable O) →
        ∃ c_star : Code,
          (Os.foldl (fun acc O => acc && O c_star) (d₀ c_star) = true) ↔ c_star ∉ Spec) ∧
    (∀ k x y : ℕ, Computable (fun c : Code => decide (Code.evaln k c x = some y))) ∧
    (∀ (Ax : Set (CForm A C)) (S : Set (Rule A C)) (Ext : Set (CForm A C))
       (v_real v_drift : CVal A C) (G_star : CForm A C),
      (∀ p ∈ Ax, IsBase p) → PropUniformRules S →
      Consistent (Ax ∪ {γ | ∃ r ∈ S, r.conseq = γ}) →
      IsExtension Ax S Ext → IsBase G_star →
      Models Ax v_real → eval v_real G_star = true →
      Models Ax v_drift → eval v_drift G_star = false →
      G_star ∉ Ext ∧ neg G_star ∉ Ext) ∧
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
