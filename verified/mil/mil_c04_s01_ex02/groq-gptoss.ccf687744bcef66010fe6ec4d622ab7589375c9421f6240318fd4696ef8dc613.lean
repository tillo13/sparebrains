import Mathlib

open Set

/-- Mathematics in Lean, Chapter 4 §1 (Sets), exercise 2. Avigad & Massot, Apache-2.0, commit dd6d752. -/
theorem mil_c04_s01_ex02 {α : Type*} (s t u : Set α) : s \ (t ∪ u) ⊆ (s \ t) \ u := by
  intro x hx
  rcases hx with ⟨hs, hnot⟩
  have ht : x ∉ t := by
    intro hxt
    apply hnot
    exact Or.inl hxt
  have hu : x ∉ u := by
    intro hxu
    apply hnot
    exact Or.inr hxu
  exact ⟨⟨hs, ht⟩, hu⟩
