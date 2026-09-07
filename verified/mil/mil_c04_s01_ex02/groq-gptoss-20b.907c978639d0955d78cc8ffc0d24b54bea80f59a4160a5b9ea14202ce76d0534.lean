import Mathlib

open Set

/-- Mathematics in Lean, Chapter 4 §1 (Sets), exercise 2. Avigad & Massot, Apache-2.0, commit dd6d752. -/
theorem mil_c04_s01_ex02 {α : Type*} (s t u : Set α) : s \ (t ∪ u) ⊆ (s \ t) \ u := by
  intro x hx
  rcases hx with ⟨hxS, hxNot⟩
  have hxNot_t : x ∉ t := by
    intro hxT
    exact hxNot (Or.inl hxT)
  have hxNot_u : x ∉ u := by
    intro hxU
    exact hxNot (Or.inr hxU)
  exact ⟨⟨hxS, hxNot_t⟩, hxNot_u⟩
