import Definitions.Def_TranscendenceTowerReification

set_option autoImplicit false

open TranscendenceTower TranscendenceTower.Reification

theorem solution : ∀ (State : Type) (c c' : State), c ≠ c' → ∀ (S S' : Set L0),
    ∃ F : RFamily State, SatCLat F S c ∧ SatCLat F S' c' := by
  intro State c c' h S S'
  -- The extension of `True₀` is `S` at `c` and `S'` everywhere else.  Phrasing
  -- it propositionally avoids needing decidable equality on `State`.
  refine ⟨⟨fun _ _ => false,
           fun d => {p | (d = c ∧ p ∈ S) ∨ (d ≠ c ∧ p ∈ S')}⟩, ?_, ?_⟩
  · intro p
    show ((c = c ∧ p ∈ S) ∨ (c ≠ c ∧ p ∈ S')) ↔ p ∈ S
    constructor
    · rintro (⟨_, hp⟩ | ⟨hne, _⟩)
      · exact hp
      · exact absurd rfl hne
    · intro hp
      exact Or.inl ⟨rfl, hp⟩
  · intro p
    show ((c' = c ∧ p ∈ S) ∨ (c' ≠ c ∧ p ∈ S')) ↔ p ∈ S'
    constructor
    · rintro (⟨he, _⟩ | ⟨_, hp⟩)
      · exact absurd he (Ne.symm h)
      · exact hp
    · intro hp
      exact Or.inr ⟨Ne.symm h, hp⟩
