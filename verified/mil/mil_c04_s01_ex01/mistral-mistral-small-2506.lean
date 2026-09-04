import Mathlib

open Set

/-- Mathematics in Lean, Chapter 4 §1 (Sets), exercise 1. Avigad & Massot, Apache-2.0, commit dd6d752. -/
theorem mil_c04_s01_ex01 {α : Type*} (s t u : Set α) : s ∩ t ∪ s ∩ u ⊆ s ∩ (t ∪ u) := by
  intro x hx
  rcases hx with (h | h)
  · rcases h with ⟨hx1, hx2⟩
    constructor
    · exact hx1
    · left
      exact hx2
  · rcases h with ⟨hx1, hx2⟩
    constructor
    · exact hx1
    · right
      exact hx2
