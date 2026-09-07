import Mathlib

open Set

/-- Mathematics in Lean, Chapter 4 §1 (Sets), exercise 2. Avigad & Massot, Apache-2.0, commit dd6d752. -/
theorem mil_c04_s01_ex02 {α : Type*} (s t u : Set α) : s \ (t ∪ u) ⊆ (s \ t) \ u := by
  intro x hx
  -- hx : x ∈ s ∧ x ∉ t ∪ u
  have h1 : x ∈ s := hx.1
  have h2 : x ∉ t ∪ u := hx.2
  -- From x ∉ t ∪ u, we deduce x ∉ t and x ∉ u using De Morgan's laws
  have h3 : x ∉ t := by
    intro ht
    -- If x ∈ t, then x ∈ t ∪ u, contradicting h2
    have h4 : x ∈ t ∪ u := Or.inl ht
    exact h2 h4
  have h4 : x ∉ u := by
    intro hu
    -- If x ∈ u, then x ∈ t ∪ u, contradicting h2
    have h5 : x ∈ t ∪ u := Or.inr hu
    exact h2 h5
  -- Now we have x ∈ s, x ∉ t, and x ∉ u
  -- Therefore x ∈ s \ t and x ∉ u, so x ∈ (s \ t) \ u
  exact ⟨⟨h1, h3⟩, h4⟩
