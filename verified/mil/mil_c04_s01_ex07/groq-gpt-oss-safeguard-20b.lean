import Mathlib

open Set

/-- Mathematics in Lean, Chapter 4 §1 (Sets), exercise 7. Avigad & Massot, Apache-2.0, commit dd6d752. -/
theorem mil_c04_s01_ex07 {α : Type*} (s t : Set α) : s \ t ∪ t \ s = (s ∪ t) \ (s ∩ t) := by
  ext x
  constructor
  · intro hx
    rcases hx with hx | hx
    · -- case `x ∈ s \ t`
      rcases hx with ⟨hx_s, hx_not_t⟩
      have hx_union : x ∈ s ∪ t := Or.inl hx_s
      have hx_not_inter : x ∉ s ∩ t := by
        intro hx_inter
        rcases hx_inter with ⟨_, hx_t⟩
        exact hx_not_t hx_t
      exact ⟨hx_union, hx_not_inter⟩
    · -- case `x ∈ t \ s`
      rcases hx with ⟨hx_t, hx_not_s⟩
      have hx_union : x ∈ s ∪ t := Or.inr hx_t
      have hx_not_inter : x ∉ s ∩ t := by
        intro hx_inter
        rcases hx_inter with ⟨hx_s, _⟩
        exact hx_not_s hx_s
      exact ⟨hx_union, hx_not_inter⟩
  · intro hx
    rcases hx with ⟨hx_union, hx_not_inter⟩
    rcases hx_union with hx_s | hx_t
    · -- `x ∈ s`
      have hx_not_t : x ∉ t := by
        intro hx_t
        have : x ∈ s ∩ t := ⟨hx_s, hx_t⟩
        exact hx_not_inter this
      exact Or.inl ⟨hx_s, hx_not_t⟩
    · -- `x ∈ t`
      have hx_not_s : x ∉ s := by
        intro hx_s
        have : x ∈ s ∩ t := ⟨hx_s, hx_t⟩
        exact hx_not_inter this
      exact Or.inr ⟨hx_t, hx_not_s⟩
