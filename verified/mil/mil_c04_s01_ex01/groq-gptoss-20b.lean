import Mathlib

open Set

/-- Mathematics in Lean, Chapter 4 §1 (Sets), exercise 1. Avigad & Massot, Apache-2.0, commit dd6d752. -/
theorem mil_c04_s01_ex01 {α : Type*} (s t u : Set α) : s ∩ t ∪ s ∩ u ⊆ s ∩ (t ∪ u) := by
  intro x hx
  rcases hx with hx | hx
  · rcases hx with ⟨hx_s, hx_t⟩
    exact ⟨hx_s, Or.inl hx_t⟩
  · rcases hx with ⟨hx_s, hx_u⟩
    exact ⟨hx_s, Or.inr hx_u⟩
