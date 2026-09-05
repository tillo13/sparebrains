import Mathlib

open Set

/-- Mathematics in Lean, Chapter 4 §1 (Sets), exercise 2. Avigad & Massot, Apache-2.0, commit dd6d752. -/
theorem mil_c04_s01_ex02 {α : Type*} (s t u : Set α) : s \ (t ∪ u) ⊆ (s \ t) \ u := by
  rintro x ⟨hs, htu⟩
  constructor
  · exact ⟨hs, fun ht => htu ((mem_union x t u).2 (Or.inl ht))⟩
  · exact fun hu => htu ((mem_union x t u).2 (Or.inr hu))
