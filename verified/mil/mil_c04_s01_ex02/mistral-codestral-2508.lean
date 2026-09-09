import Mathlib

open Set

/-- Mathematics in Lean, Chapter 4 §1 (Sets), exercise 2. Avigad & Massot, Apache-2.0, commit dd6d752. -/
theorem mil_c04_s01_ex02 {α : Type*} (s t u : Set α) : s \ (t ∪ u) ⊆ (s \ t) \ u := by
  intro x hx
  have hx1 : x ∈ s := hx.1
  have hx2 : x ∉ t ∪ u := hx.2
  have hx3 : x ∉ t := by
    intro hxt
    have hxtu : x ∈ t ∪ u := Or.inl hxt
    contradiction
  have hx4 : x ∉ u := by
    intro hxu
    have hxtu : x ∈ t ∪ u := Or.inr hxu
    contradiction
  have hx5 : x ∈ s \ t := ⟨hx1, hx3⟩
  exact ⟨hx5, hx4⟩
