import Mathlib

open Set

/-- Mathematics in Lean, Chapter 4 §1 (Sets), exercise 6. Avigad & Massot, Apache-2.0, commit dd6d752. -/
theorem mil_c04_s01_ex06 {α : Type*} (s t : Set α) : s \ t ∪ t = s ∪ t := by
  ext x
  constructor
  · intro h
    cases h with
    | inl h' => exact Or.inl h'.left
    | inr h' => exact Or.inr h'
  · intro h
    cases h with
    | inl h' =>
      by_cases xt : x ∈ t
      · exact Or.inr xt
      · exact Or.inl (Set.mem_sdiff_of_mem h' xt)
    | inr h' => exact Or.inr h'
