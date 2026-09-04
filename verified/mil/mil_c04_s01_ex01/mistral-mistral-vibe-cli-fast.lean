import Mathlib

open Set

/-- Mathematics in Lean, Chapter 4 §1 (Sets), exercise 1. Avigad & Massot, Apache-2.0, commit dd6d752. -/
theorem mil_c04_s01_ex01 {α : Type*} (s t u : Set α) : s ∩ t ∪ s ∩ u ⊆ s ∩ (t ∪ u) := by
  intro x h
  simp only [Set.mem_union, Set.mem_inter, Set.mem_setOf_eq] at h ⊢
  rcases h with (⟨hxs, hxt⟩ | ⟨hxs, hxu⟩)
  · exact ⟨hxs, Or.inl hxt⟩
  · exact ⟨hxs, Or.inr hxu⟩
