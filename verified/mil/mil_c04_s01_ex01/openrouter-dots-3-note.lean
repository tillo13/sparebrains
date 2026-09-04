import Mathlib

open Set

/-- Mathematics in Lean, Chapter 4 §1 (Sets), exercise 1. Avigad & Massot, Apache-2.0, commit dd6d752. -/
theorem mil_c04_s01_ex01 {α : Type*} (s t u : Set α) : s ∩ t ∪ s ∩ u ⊆ s ∩ (t ∪ u) := by
  intro x
  intro h
  rcases h with h1 | h2
  · constructor
    · exact h1.1
    · left
      exact h1.2
  · constructor
    · exact h2.1
    · right
      exact h2.2
