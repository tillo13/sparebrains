import Mathlib

open Set

/-- Mathematics in Lean, Chapter 4 §1 (Sets), exercise 2. Avigad & Massot, Apache-2.0, commit dd6d752. -/
theorem mil_c04_s01_ex02 {α : Type*} (s t u : Set α) : s \ (t ∪ u) ⊆ (s \ t) \ u := by
  intro x hx
  rcases hx with ⟨hxS, hxNotTU⟩
  have hxNotT : x ∉ t := by
    intro hxT
    exact hxNotTU (Or.inl hxT)
  have hxNotU : x ∉ u := by
    intro hxU
    exact hxNotTU (Or.inr hxU)
  exact ⟨⟨hxS, hxNotT⟩, hxNotU⟩
