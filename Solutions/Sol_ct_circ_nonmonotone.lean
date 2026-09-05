import Definitions.Def_TranscendenceTowerBirdDefault

set_option autoImplicit false

open TranscendenceTower TranscendenceTower.ContextTheories

theorem cn_mono' {T T' : Set L0} (h : T ⊆ T') : Cn T ⊆ Cn T' :=
  fun _ hp v hv => hp v (fun q hq => hv q (h hq))

theorem tsmall_sub' : Tsmall ⊆ Tbig := by
  intro p hp
  rcases hp with h | h
  · exact Or.inl h
  · exact Or.inr (Or.inl h)

theorem models_small_normal' : Models Tsmall vNormal := by
  rintro p (rfl | rfl) <;> rfl

theorem models_big_abnormal' : Models Tbig vAbnormal := by
  rintro p (rfl | rfl | rfl) <;> rfl

theorem abset_normal' : AbSet abAtoms vNormal = ∅ := by
  ext k
  constructor
  · rintro ⟨hk, hv⟩
    rw [show k = 2 from hk] at hv
    exact absurd hv (by decide)
  · intro h
    exact absurd h (by simp)

theorem not_abnormal' {v : Val} (h : MinModel abAtoms Tsmall v) : v 2 = false := by
  by_contra hv
  have hv2 : v 2 = true := by
    cases hvv : v 2 with
    | false => exact absurd hvv hv
    | true => rfl
  have hmem : (2 : Base) ∈ AbSet abAtoms v := ⟨rfl, hv2⟩
  have hsub : AbSet abAtoms vNormal ⊆ AbSet abAtoms v := by
    rw [abset_normal']; exact Set.empty_subset _
  have hv' := h.2 vNormal models_small_normal' hsub
  rw [abset_normal'] at hv'
  exact absurd (hv' hmem) (by simp)

theorem flies_small' : flies ∈ CnCirc abAtoms Tsmall := by
  intro v hv
  have hab : v 2 = false := not_abnormal' hv
  have hbird : Form.eval v bird = true := hv.1 bird (Or.inl rfl)
  have hdef : Form.eval v defaultRule = true := hv.1 defaultRule (Or.inr rfl)
  show v 1 = true
  simp only [defaultRule, bird, flies, abn, Form.eval] at hdef
  simp only [bird, Form.eval] at hbird
  rw [hbird, hab] at hdef
  simpa using hdef

theorem minmodel_big' : MinModel abAtoms Tbig vAbnormal := by
  refine ⟨models_big_abnormal', fun w hw _ => ?_⟩
  rintro k ⟨hk, _⟩
  rw [show k = 2 from hk]
  exact ⟨rfl, hw abn (Or.inr (Or.inr rfl))⟩

theorem flies_not_big' : flies ∉ CnCirc abAtoms Tbig := by
  intro h
  exact absurd (h vAbnormal minmodel_big') (by decide)


theorem solution :
    (∀ T T' : Set L0, T ⊆ T' → Cn T ⊆ Cn T')
      ∧ ∃ (ab : Set Base) (T T' : Set L0) (φ : L0),
          T' ⊆ T ∧ φ ∈ CnCirc ab T' ∧ φ ∉ CnCirc ab T :=
  ⟨fun _ _ h => cn_mono' h,
   ⟨abAtoms, Tbig, Tsmall, flies, tsmall_sub', flies_small', flies_not_big'⟩⟩
