import Mathlib

open Set

/-- Mathematics in Lean, Chapter 4 §1 (Sets), exercise 6. Avigad & Massot, Apache-2.0, commit dd6d752. -/
theorem mil_c04_s01_ex06 {α : Type*} (s t : Set α) : s \ t ∪ t = s ∪ t := by
  have h_main : s \ t ∪ t = s ∪ t := by
    apply Set.ext
    intro x
    simp only [Set.mem_union, Set.mem_diff, Set.mem_singleton_iff] at *
    <;>
    by_cases hx : x ∈ t <;>
    by_cases hy : x ∈ s <;>
    simp_all [hx, hy]
    <;>
    tauto
  
  rw [h_main]
  <;>
  simp_all
