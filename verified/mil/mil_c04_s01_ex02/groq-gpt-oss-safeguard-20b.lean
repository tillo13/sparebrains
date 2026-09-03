import Mathlib

open Set

/-- Mathematics in Lean, Chapter 4 §1 (Sets), exercise 2. Avigad & Massot, Apache-2.0, commit dd6d752. -/
theorem mil_c04_s01_ex02 {α : Type*} (s t u : Set α) : s \ (t ∪ u) ⊆ (s \ t) \ u := by
  intro x hx
  rcases hx with ⟨hx_s, hx_not_tu⟩
  have hx_not_t : x ∉ t := by
    intro hx_t
    exact hx_not_tu (Or.inl hx_t)
  have hx_not_u : x ∉ u := by
    intro hx_u
    exact hx_not_tu (Or.inr hx_u)
  exact ⟨⟨hx_s, hx_not_t⟩, hx_not_u⟩
