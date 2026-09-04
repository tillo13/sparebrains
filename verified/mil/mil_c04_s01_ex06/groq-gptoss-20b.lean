import Mathlib

open Set

/-- Mathematics in Lean, Chapter 4 §1 (Sets), exercise 6. Avigad & Massot, Apache-2.0, commit dd6d752. -/
theorem mil_c04_s01_ex06 {α : Type*} (s t : Set α) : s \ t ∪ t = s ∪ t := by
  ext x
  constructor
  · intro hx
    rcases hx with hx | hx
    · exact Or.inl hx.1
    · exact Or.inr hx
  · intro hx
    rcases hx with hx | hx
    · by_cases hxt : x ∈ t
      · exact Or.inr hxt
      · exact Or.inl ⟨hx, hxt⟩
    · exact Or.inr hx
