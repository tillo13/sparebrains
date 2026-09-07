import Mathlib

open Set

/-- Mathematics in Lean, Chapter 4 §1 (Sets), exercise 6. Avigad & Massot, Apache-2.0, commit dd6d752. -/
theorem mil_c04_s01_ex06 {α : Type*} (s t : Set α) : s \ t ∪ t = s ∪ t := by
  have h_subset : s \ t ∪ t ⊆ s ∪ t := by
    intro x hx
    simp only [Set.mem_union, Set.mem_diff] at hx ⊢
    -- Now hx is (x ∈ s ∧ x ∉ t) ∨ x ∈ t, and we need to prove x ∈ s ∨ x ∈ t
    cases hx with
    | inl hx =>
      -- Case: x ∈ s ∧ x ∉ t
      exact Or.inl hx.1
    | inr hx =>
      -- Case: x ∈ t
      exact Or.inr hx
  
  have h_superset : s ∪ t ⊆ s \ t ∪ t := by
    intro x hx
    simp only [Set.mem_union, Set.mem_diff] at hx ⊢
    -- Now hx is x ∈ s ∨ x ∈ t, and we need to prove (x ∈ s ∧ x ∉ t) ∨ x ∈ t
    cases hx with
    | inl hx =>
      -- Case: x ∈ s
      by_cases hxt : x ∈ t
      · -- Subcase: x ∈ t
        exact Or.inr hxt
      · -- Subcase: x ∉ t
        exact Or.inl ⟨hx, hxt⟩
    | inr hx =>
      -- Case: x ∈ t
      exact Or.inr hx
  
  have h_main : s \ t ∪ t = s ∪ t := by
    apply Set.Subset.antisymm
    · -- Prove s \ t ∪ t ⊆ s ∪ t
      exact h_subset
    · -- Prove s ∪ t ⊆ s \ t ∪ t
      exact h_superset
  
  exact h_main
