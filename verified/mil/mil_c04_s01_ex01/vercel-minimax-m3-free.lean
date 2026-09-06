import Mathlib

open Set

/-- Mathematics in Lean, Chapter 4 §1 (Sets), exercise 1. Avigad & Massot, Apache-2.0, commit dd6d752. -/
theorem mil_c04_s01_ex01 {α : Type*} (s t u : Set α) : s ∩ t ∪ s ∩ u ⊆ s ∩ (t ∪ u) := by
  intro x hx
  rcases hx with hx | hx
  · have hxs : x ∈ s := hx.1
    have hxt : x ∈ t := hx.2
    exact ⟨hxs, Or.inl hxt⟩
  · have hxs : x ∈ s := hx.1
    have hxu : x ∈ u := hx.2
    exact ⟨hxs, Or.inr hxu⟩
