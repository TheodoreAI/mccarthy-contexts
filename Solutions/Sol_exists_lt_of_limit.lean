import Definitions.Def_TranscendenceTowerTransfinite

set_option autoImplicit false

open TranscendenceTower.Transfinite

/-- The languages form a chain: `β ≤ α → L_β ⊆ L_α`. -/
theorem mono' {β α : Ordinal} (h : β ≤ α) {p : TForm} : InLang β p → InLang α p := by
  intro hp
  induction hp generalizing α with
  | atom k => exact InLang.atom k
  | ist hlt _ ih => exact InLang.ist (lt_of_lt_of_le hlt h) (ih le_rfl)
  | neg _ ih => exact InLang.neg (ih h)
  | conj _ _ ihp ihq => exact InLang.conj (ihp h) (ihq h)
  | disj _ _ ihp ihq => exact InLang.disj (ihp h) (ihq h)
  | impl _ _ ihp ihq => exact InLang.impl (ihp h) (ihq h)

theorem solution (lam : Ordinal) (hlim : IsLimitOrd lam) (p : TForm)
    (hp : InLang lam p) : ∃ β, β < lam ∧ InLang β p := by
  -- `induction` reverts `hlim` (it mentions the index `lam`), so each induction
  -- hypothesis takes the limit hypothesis as an argument; feed it back in.
  induction hp with
  | atom k => exact ⟨0, hlim.1, InLang.atom k⟩
  | @ist _ β q hlt hqβ _ =>
      obtain ⟨γ, hβγ, hγlam⟩ := hlim.2 β hlt
      exact ⟨γ, hγlam, InLang.ist hβγ hqβ⟩
  | neg _ ih =>
      obtain ⟨β, hβ, hq⟩ := ih hlim
      exact ⟨β, hβ, InLang.neg hq⟩
  | conj _ _ ihp ihq =>
      obtain ⟨β₁, hβ₁, h1⟩ := ihp hlim
      obtain ⟨β₂, hβ₂, h2⟩ := ihq hlim
      exact ⟨max β₁ β₂, max_lt hβ₁ hβ₂,
        InLang.conj (mono' (le_max_left _ _) h1) (mono' (le_max_right _ _) h2)⟩
  | disj _ _ ihp ihq =>
      obtain ⟨β₁, hβ₁, h1⟩ := ihp hlim
      obtain ⟨β₂, hβ₂, h2⟩ := ihq hlim
      exact ⟨max β₁ β₂, max_lt hβ₁ hβ₂,
        InLang.disj (mono' (le_max_left _ _) h1) (mono' (le_max_right _ _) h2)⟩
  | impl _ _ ihp ihq =>
      obtain ⟨β₁, hβ₁, h1⟩ := ihp hlim
      obtain ⟨β₂, hβ₂, h2⟩ := ihq hlim
      exact ⟨max β₁ β₂, max_lt hβ₁ hβ₂,
        InLang.impl (mono' (le_max_left _ _) h1) (mono' (le_max_right _ _) h2)⟩
