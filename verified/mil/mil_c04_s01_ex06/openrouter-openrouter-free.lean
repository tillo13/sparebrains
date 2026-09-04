import Mathlib

open Set

/-- Mathematics in Lean, Chapter 4 §1 (Sets), exercise 6. Avigad & Massot, Apache-2.0, commit dd6d752. -/
theorem mil_c04_s01_ex06 {α : Type*} (s t : Set α) : s \ t ∪ t = s ∪ t := by
  ext x
  constructor
  · intro h
    rcases h with h | h
    · rcases h with ⟨hs, hnt⟩
      exact Or.inl hs
    · exact Or.inr h
  · intro h
    rcases h with hs | ht
    · by_cases hxt : x ∈ t
      · exact Or.inr hxt
      · exact Or.inl ⟨hs, hxt⟩
    · exact Or.inr ht
