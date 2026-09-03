import Mathlib

open Set

/-- Mathematics in Lean, Chapter 4 §1 (Sets), exercise 2. Avigad & Massot, Apache-2.0, commit dd6d752. -/
theorem mil_c04_s01_ex02 {α : Type*} (s t u : Set α) : s \ (t ∪ u) ⊆ (s \ t) \ u := by
  have h_main : ∀ (x : α), x ∈ s \ (t ∪ u) → x ∈ (s \ t) \ u := by
    intro x hx
    have h1 : x ∈ s := by
      -- Extract the fact that x ∈ s from the hypothesis hx
      exact hx.1
    have h2 : x ∉ t ∪ u := by
      -- Extract the fact that x ∉ t ∪ u from the hypothesis hx
      exact hx.2
    have h3 : x ∉ t := by
      -- Prove that x ∉ t using the fact that x ∉ t ∪ u
      intro h
      have h4 : x ∈ t ∪ u := by
        exact Or.inl h
      exact h2 h4
    have h4 : x ∉ u := by
      -- Prove that x ∉ u using the fact that x ∉ t ∪ u
      intro h
      have h5 : x ∈ t ∪ u := by
        exact Or.inr h
      exact h2 h5
    have h5 : x ∈ s \ t := by
      -- Prove that x ∈ s \ t using h1 and h3
      exact ⟨h1, h3⟩
    have h6 : x ∈ (s \ t) \ u := by
      -- Prove that x ∈ (s \ t) \ u using h5 and h4
      exact ⟨h5, h4⟩
    exact h6
  
  -- Use the main lemma to prove the subset relation
  intro x hx
  have h : x ∈ (s \ t) \ u := h_main x hx
  exact h
