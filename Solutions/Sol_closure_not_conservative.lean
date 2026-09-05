import Definitions.Def_TranscendenceTowerReification

set_option autoImplicit false

open TranscendenceTower TranscendenceTower.Reification

/-- From `T₀` and `CL(S)` together: `φ ↔ (⌜φ⌝ ∈ S)` for every `φ ∈ L₀`. -/
theorem eval_iff_mem' {M : RStruc} {S : Set L0} (h0 : SatT0 M) (hc : SatCL M S)
    (p : L0) : Form.eval M.val p = true ↔ p ∈ S :=
  (h0 p).symm.trans (hc p)

/-- Every code outside `S` is refuted. -/
theorem closure_refutes' {M : RStruc} {S : Set L0} (h0 : SatT0 M) (hc : SatCL M S)
    {p : L0} (hp : p ∉ S) : Form.eval M.val p = false := by
  cases hv : Form.eval M.val p with
  | false => rfl
  | true => exact absurd ((eval_iff_mem' h0 hc p).mp hv) hp

theorem solution :
    ∃ (S : Set L0) (p : L0),
      (∃ M : RStruc, SatT0 M ∧ SatCL M S)
        ∧ (∀ M : RStruc, SatT0 M → SatCL M S → Form.eval M.val p = false)
        ∧ (∃ v : Val, Form.eval v p = true) := by
  refine ⟨truths (fun _ => false), Form.atom 0,
          ⟨expand (fun _ => false), fun _ => Iff.rfl, fun _ => Iff.rfl⟩,
          fun _ h0 hc => closure_refutes' h0 hc ?_,
          ⟨fun _ => true, rfl⟩⟩
  show Form.atom 0 ∉ truths (fun _ => false)
  simp [truths, Form.eval]
