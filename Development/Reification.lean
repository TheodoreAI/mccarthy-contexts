/-
  Section 4 of "Consistency of a Stratified Formalization of McCarthy's
  Transcendence Tower": reifying a level -- `truths(c₀)` and closure.

  McCarthy suggests in passing that the formalism "might be further extended to
  provide so that in c₋₁ the whole set of sentences true in c₀ is an object
  truths(c₀)".  Section 4 examines that extension.  It is where the deflationary
  reading of §3 stops applying: reifying a level is NOT a definitional
  extension, and the results below separate the part that remains harmless
  (Proposition 2) from the part that does not (Propositions 3, Theorem 4).

  Formalized here:
    Def 3   reified language L⁺₀ with `True₀`, and the schema `T₀`
    Prop 2  reification alone is harmless: `T₀` consistent AND conservative
    Def 4   the closure axiom `CL(S)`
    Prop 3  closure is not conservative
    Thm 4   distinct closure claims are jointly inconsistent
    Def 5   relativized closure `CL(S, c)`
    Prop 5  relativization restores consistency

  Method.  Every proof in §4 of the paper is semantic -- it builds a structure
  and reads the axioms off it -- so this file works with structures and
  satisfaction rather than erecting a first-order proof calculus.  Consistency
  is therefore rendered as satisfiability and conservativity as "every model of
  the smaller theory expands to one of the larger", exactly as the paper argues.

  Coding.  The paper posits a domain containing a code `⌜φ⌝` for each `φ ∈ L₀`.
  None of its arguments depend on *which* coding is used, only on there being an
  injection, so we identify codes with the formulas they code and let `True₀` be
  a set of formulas.  This is faithful and avoids an irrelevant Gödel-numbering
  layer.

  Self-contained: the small propositional core is repeated here (rather than
  imported) so the file compiles standalone with `lake env lean`.
-/

import Mathlib.Data.Set.Basic

set_option autoImplicit false

namespace TranscendenceTower.Reification

/-! ## The base language `L₀` -/

/-- Formulas of `L₀`: classical propositional logic over countably many atoms. -/
inductive Form where
  | atom : Nat → Form
  | neg  : Form → Form
  | conj : Form → Form → Form
  | disj : Form → Form → Form
  | impl : Form → Form → Form

/-- A valuation of `L₀`. -/
abbrev Val := Nat → Bool

/-- Classical truth-table evaluation. -/
def eval (v : Val) : Form → Bool
  | Form.atom k   => v k
  | Form.neg p    => !(eval v p)
  | Form.conj p q => (eval v p) && (eval v q)
  | Form.disj p q => (eval v p) || (eval v q)
  | Form.impl p q => !(eval v p) || (eval v q)

/-- `truths(c₀)`: the set of `L₀`-sentences true under a valuation.  This is the
object McCarthy proposes to reify. -/
def truths (v : Val) : Set Form := {p | eval v p = true}

/-! ## Definition 3 — the reified language

A predicate that merely holds of true `L₀`-formulas is nothing new -- that is
`ist₀` under another name.  The new capability is quantification over the level,
which is why `True₀` is a genuine predicate on a domain of codes.

Tarski's undefinability theorem is sometimes misread as forbidding this.  It
does not: it forbids a sufficiently strong language from defining *its own*
truth predicate.  Here `True₀` lives one level up from the language it
describes, which is precisely the stratified arrangement Tarski proposed as the
remedy. -/

/-- A structure for the reified language `L⁺₀`: a valuation of `L₀` together
with an interpretation of the unary predicate `True₀`. -/
structure RStruc where
  /-- The `L₀`-reduct. -/
  val : Val
  /-- The extension of `True₀`, as a set of codes. -/
  True0 : Set Form

/-- **Definition 3.** The schema `T₀ : True₀(⌜φ⌝) ↔ φ`, for every `φ ∈ L₀`. -/
def SatT0 (M : RStruc) : Prop :=
  ∀ p : Form, p ∈ M.True0 ↔ eval M.val p = true

/-- The canonical expansion of a valuation: interpret `True₀` as the set of
codes of its true formulas. -/
def expand (v : Val) : RStruc := ⟨v, truths v⟩

theorem satT0_expand (v : Val) : SatT0 (expand v) := fun _ => Iff.rfl

/-- The expansion does not disturb the `L₀`-reduct. -/
theorem expand_val (v : Val) : (expand v).val = v := rfl

/-! ## Proposition 2 — reification alone is harmless -/

/-- **Proposition 2**, consistency half: `T₀` is satisfiable. -/
theorem T0_consistent : ∃ M : RStruc, SatT0 M :=
  ⟨expand (fun _ => false), satT0_expand _⟩

/-- **Proposition 2**, conservativity half: `T₀` proves no new `L₀`-sentence.

The paper's argument verbatim: every valuation `M₀` extends to a model of `T₀`,
so an `L₀`-sentence false in some model of `L₀` stays false in some model of
`T₀`.  Contrapositively, an `L₀`-sentence true in every model of `T₀` is true
under every valuation. -/
theorem T0_conservative (p : Form)
    (h : ∀ M : RStruc, SatT0 M → eval M.val p = true) :
    ∀ v : Val, eval v p = true :=
  fun v => h (expand v) (satT0_expand v)

/-- The same fact stated as an expansion property, which is what conservativity
rests on: every `L₀`-model is the reduct of a model of `T₀`. -/
theorem exists_model_with_reduct (v : Val) :
    ∃ M : RStruc, SatT0 M ∧ M.val = v :=
  ⟨expand v, satT0_expand v, rfl⟩

/-! ## Definition 4 — the closure axiom -/

/-- **Definition 4.** `CL(S) : ∀x (True₀(x) ↔ x ∈ S)`, for an explicitly given
set `S` of codes.

This is a closed-world assumption, and the nonmonotonic machinery it uses is
McCarthy's own invention: `CL(S)` is a circumscription of `True₀`.  The negative
information it supplies -- "nothing else is true here" -- is precisely the
content that cannot be obtained by definitional extension, which is why the
consistency result of §3 does not cover it. -/
def SatCL (M : RStruc) (S : Set Form) : Prop :=
  ∀ p : Form, p ∈ M.True0 ↔ p ∈ S

/-- From `T₀` and `CL(S)` together: `φ ↔ (⌜φ⌝ ∈ S)` for every `φ ∈ L₀`.
This single equivalence drives both Proposition 3 and Theorem 4. -/
theorem eval_iff_mem {M : RStruc} {S : Set Form} (h0 : SatT0 M)
    (hc : SatCL M S) (p : Form) : eval M.val p = true ↔ p ∈ S :=
  (h0 p).symm.trans (hc p)

/-! ## Proposition 3 — closure is where content enters -/

/-- Every code outside `S` is *refuted*: `T₀ + CL(S) ⊢ ¬φ` whenever `⌜φ⌝ ∉ S`. -/
theorem closure_refutes {M : RStruc} {S : Set Form} (h0 : SatT0 M)
    (hc : SatCL M S) {p : Form} (hp : p ∉ S) : eval M.val p = false := by
  cases hv : eval M.val p with
  | false => rfl
  | true => exact absurd ((eval_iff_mem h0 hc p).mp hv) hp

/-- **Proposition 3** (closure is not conservative).

Stated so as to be non-vacuous, which takes some care.  A carelessly chosen `S`
makes `T₀ + CL(S)` *unsatisfiable* -- with `S = ∅`, for instance, since
`truths(v)` always contains tautologies such as `p → p`, so `True₀` can never
have empty extension in a model of `T₀`.  A refutation claim about a theory with
no models establishes nothing.

So we take `S` to be an honest completeness claim, `truths(v₀)` for a real
valuation.  Then all three conjuncts have force: the theory *is* satisfiable, it
refutes `p₁`, and yet `p₁` is satisfiable in `L₀` alone -- the base language,
having asserted nothing about it, proves neither it nor its negation.  The
closure axiom has therefore added genuinely new `L₀`-content. -/
theorem closure_not_conservative :
    ∃ (S : Set Form) (p : Form),
      (∃ M : RStruc, SatT0 M ∧ SatCL M S)
        ∧ (∀ M : RStruc, SatT0 M → SatCL M S → eval M.val p = false)
        ∧ (∃ v : Val, eval v p = true) := by
  refine ⟨truths (fun _ => false), Form.atom 0,
          ⟨expand (fun _ => false), satT0_expand _, fun _ => Iff.rfl⟩,
          fun _ h0 hc => closure_refutes h0 hc ?_,
          ⟨fun _ => true, rfl⟩⟩
  show Form.atom 0 ∉ truths (fun _ => false)
  simp [truths, eval]

/-- The hazard that made the care above necessary, recorded explicitly: a
closure claim can be not merely wrong but *unsatisfiable*.  In any model of `T₀`
the extension of `True₀` contains every tautology, so `T₀ + CL(∅)` has no
models at all. -/
theorem T0_CL_empty_unsatisfiable :
    ¬ ∃ M : RStruc, SatT0 M ∧ SatCL M ∅ := by
  rintro ⟨M, h0, hc⟩
  have taut : eval M.val (Form.impl (Form.atom 0) (Form.atom 0)) = true := by
    cases h : M.val 0 <;> simp [eval, h]
  simpa using (eval_iff_mem h0 hc _).mp taut

/-! ## Theorem 4 — two closure claims collide -/

/-- **Theorem 4** (distinct closure claims are jointly inconsistent).

If `S ≠ S'` then `T₀ + CL(S) + CL(S')` has no model.  Two completeness claims
about the same level, each honestly made, cannot both be held merely because
each was made in good faith. -/
theorem closure_collide {S S' : Set Form} (h : S ≠ S') :
    ¬ ∃ M : RStruc, SatT0 M ∧ SatCL M S ∧ SatCL M S' := by
  rintro ⟨M, _, hS, hS'⟩
  exact h (Set.ext fun p => (hS p).symm.trans (hS' p))

/-- Theorem 4 by the paper's own argument, which exhibits the contradictory
sentence: pick `⌜φ⌝ ∈ S \ S'`; then `CL(S)` yields `φ` and `CL(S')` yields
`¬φ`. -/
theorem closure_collide_witness {M : RStruc} {S S' : Set Form} (h0 : SatT0 M)
    (hS : SatCL M S) (hS' : SatCL M S') {p : Form} (hpS : p ∈ S)
    (hpS' : p ∉ S') : False := by
  have h1 : eval M.val p = true := (eval_iff_mem h0 hS p).mpr hpS
  have h2 : eval M.val p = false := closure_refutes h0 hS' hpS'
  rw [h1] at h2
  exact Bool.noConfusion h2

/-- The contrast the paper draws: *ordinary* assertions about a level coexist
without difficulty.  Asserting that one sentence is true and another false is
jointly satisfiable together with `T₀`, whereas by `closure_collide` two closure
claims of different extent never are. -/
theorem ordinary_claims_coexist :
    ∃ M : RStruc, SatT0 M ∧ Form.atom 0 ∈ M.True0 ∧ Form.atom 1 ∉ M.True0 := by
  refine ⟨expand (fun k => k == 0), satT0_expand _, ?_, ?_⟩
  · show eval (fun k => k == 0) (Form.atom 0) = true
    rfl
  · show ¬ (eval (fun k => k == 0) (Form.atom 1) = true)
    simp [eval]

/-! ## Definition 5 and Proposition 5 — relativization restores consistency -/

/-- **Definition 5.** A state-indexed family of reified structures.  `CL(S, c)`
will assert that, relative to state `c`, the extension of `True₀` is exactly
`S`. -/
structure RFamily (State : Type) where
  /-- The `L₀`-reduct at each state. -/
  val : State → Val
  /-- The extension of `True₀` at each state. -/
  True0 : State → Set Form

/-- `CL(S, c)`: relative to state `c`, the extension of `True₀` is exactly `S`. -/
def SatCLat {State : Type} (F : RFamily State) (S : Set Form) (c : State) : Prop :=
  ∀ p : Form, p ∈ F.True0 c ↔ p ∈ S

/-- **Proposition 5** (relativization restores consistency).

For `c ≠ c'`, `CL(S,c)` and `CL(S',c')` are jointly satisfiable for *any* `S`
and `S'`.  The two axioms constrain the predicate at different indices, so the
derivation of Theorem 4 -- which required both claims to constrain the same
extension -- is unavailable.

Note on scope, matching the paper: this proposition is about the closure axioms
themselves.  Adding the relativized Tarski schema as well constrains `S` and
`S'` to be truth-sets of the corresponding valuations; that stronger statement
is `relativized_satisfiable_with_T0` below. -/
theorem relativized_satisfiable {State : Type} [DecidableEq State]
    {c c' : State} (h : c ≠ c') (S S' : Set Form) :
    ∃ F : RFamily State, SatCLat F S c ∧ SatCLat F S' c' := by
  refine ⟨⟨fun _ _ => false, fun d => if d = c then S else S'⟩, fun p => ?_, fun p => ?_⟩
  · show p ∈ (if c = c then S else S') ↔ p ∈ S
    rw [if_pos rfl]
  · show p ∈ (if c' = c then S else S') ↔ p ∈ S'
    rw [if_neg (Ne.symm h)]

/-- The strengthening that carries the moral: if `S` and `S'` are each an honest
completeness claim -- the truth-set of *some* state -- then the relativized
closure claims are jointly satisfiable **together with** the relativized Tarski
schema.

This is the precise sense in which a completeness claim must carry the state it
was computed against.  An unrelativized closure claim is not merely imprecise;
by Theorem 4 it is incompatible with any other closure claim of different
extent, including one made later by the same agent about the same level after
the level has changed.  Relativization is what makes a completeness claim into
something that can be superseded rather than contradicted. -/
theorem relativized_satisfiable_with_T0 {State : Type} [DecidableEq State]
    {c c' : State} (h : c ≠ c') (v v' : Val) :
    ∃ F : RFamily State,
      (∀ (d : State) (p : Form), p ∈ F.True0 d ↔ eval (F.val d) p = true)
        ∧ SatCLat F (truths v) c ∧ SatCLat F (truths v') c' := by
  refine ⟨⟨fun d => if d = c then v else v',
           fun d => truths (if d = c then v else v')⟩, fun _ _ => Iff.rfl,
          fun p => ?_, fun p => ?_⟩
  · show p ∈ truths (if c = c then v else v') ↔ p ∈ truths v
    rw [if_pos rfl]
  · show p ∈ truths (if c' = c then v else v') ↔ p ∈ truths v'
    rw [if_neg (Ne.symm h)]

/-! ## Verification -/

section Verification

/-- Proposition 2 restated inline: consistent *and* conservative. -/
example : (∃ M : RStruc, SatT0 M)
    ∧ (∀ v : Val, ∃ M : RStruc, SatT0 M ∧ M.val = v) :=
  ⟨T0_consistent, exists_model_with_reduct⟩

/-- Theorem 4 restated inline. -/
example : ∀ (S S' : Set Form), S ≠ S' →
    ¬ ∃ M : RStruc, SatT0 M ∧ SatCL M S ∧ SatCL M S' :=
  fun _ _ h => closure_collide h

/-- Proposition 5 restated inline, with `State := Bool` to confirm the
hypothesis `c ≠ c'` is satisfiable and the statement is not vacuous. -/
example : ∀ (S S' : Set Form), ∃ F : RFamily Bool,
    SatCLat F S true ∧ SatCLat F S' false :=
  fun S S' => relativized_satisfiable (by decide) S S'

#print axioms T0_consistent
#print axioms T0_conservative
#print axioms exists_model_with_reduct
#print axioms eval_iff_mem
#print axioms closure_refutes
#print axioms closure_not_conservative
#print axioms T0_CL_empty_unsatisfiable
#print axioms closure_collide
#print axioms closure_collide_witness
#print axioms ordinary_claims_coexist
#print axioms relativized_satisfiable
#print axioms relativized_satisfiable_with_T0

end Verification

end TranscendenceTower.Reification
