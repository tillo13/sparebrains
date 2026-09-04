import Mathlib

open Set

/-- Mathematics in Lean, Chapter 4 §1 (Sets), exercise 7. Avigad & Massot, Apache-2.0, commit dd6d752. -/
theorem mil_c04_s01_ex07 {α : Type*} (s t : Set α) : s \ t ∪ t \ s = (s ∪ t) \ (s ∩ t) := by
  apply Set.ext
  intro x
  constructor
  · -- Prove forward direction: if x ∈ s \ t ∪ t \ s then x ∈ (s ∪ t) \ (s ∩ t)
    intro h
    cases h with
    | inl h =>
      -- Case: x ∈ s \ t
      have h₁ : x ∈ s := h.1
      have h₂ : x ∉ t := h.2
      have h₃ : x ∈ s ∪ t := Or.inl h₁
      have h₄ : ¬(x ∈ s ∧ x ∈ t) := by
        intro h₄
        have h₅ : x ∈ t := h₄.2
        exact h₂ h₅
      exact ⟨h₃, h₄⟩
    | inr h =>
      -- Case: x ∈ t \ s
      have h₁ : x ∈ t := h.1
      have h₂ : x ∉ s := h.2
      have h₃ : x ∈ s ∪ t := Or.inr h₁
      have h₄ : ¬(x ∈ s ∧ x ∈ t) := by
        intro h₄
        have h₅ : x ∈ s := h₄.1
        exact h₂ h₅
      exact ⟨h₃, h₄⟩
  · -- Prove reverse direction: if x ∈ (s ∪ t) \ (s ∩ t) then x ∈ s \ t ∪ t \ s
    intro h
    have h₁ : x ∈ s ∪ t := h.1
    have h₂ : ¬(x ∈ s ∧ x ∈ t) := h.2
    have h₃ : x ∉ s ∨ x ∉ t := by
      by_contra! h₄
      -- If both x ∈ s and x ∈ t, then contradiction with h₂
      have h₄ : x ∈ s := by tauto
      have h₅ : x ∈ t := by tauto
      exact h₂ ⟨h₄, h₅⟩
    cases h₃ with
    | inl h₃ =>
      -- Case: x ∉ s
      have h₄ : x ∈ t := by
        -- Since x ∈ s ∪ t and x ∉ s, we must have x ∈ t
        cases h₁ with
        | inl h₁ =>
          exfalso
          exact h₃ h₁
        | inr h₁ =>
          exact h₁
      have h₅ : x ∈ t \ s := ⟨h₄, h₃⟩
      exact Or.inr h₅
    | inr h₃ =>
      -- Case: x ∉ t
      have h₄ : x ∈ s := by
        -- Since x ∈ s ∪ t and x ∉ t, we must have x ∈ s
        cases h₁ with
        | inl h₁ =>
          exact h₁
        | inr h₁ =>
          exfalso
          exact h₃ h₁
      have h₅ : x ∈ s \ t := ⟨h₄, h₃⟩
      exact Or.inl h₅
