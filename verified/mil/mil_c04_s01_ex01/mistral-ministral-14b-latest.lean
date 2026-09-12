import Mathlib

open Set

/-- Mathematics in Lean, Chapter 4 §1 (Sets), exercise 1. Avigad & Massot, Apache-2.0, commit dd6d752. -/
theorem mil_c04_s01_ex01 {α : Type*} (s t u : Set α) : s ∩ t ∪ s ∩ u ⊆ s ∩ (t ∪ u) := by
  intro x hx
  rcases hx with (hx1 | hx2)
  · rcases hx1 with ⟨hx1s, hx1t⟩
    exact ⟨hx1s, Or.inl hx1t⟩
  · rcases hx2 with ⟨hx2s, hx2u⟩
    exact ⟨hx2s, Or.inr hx2u⟩
