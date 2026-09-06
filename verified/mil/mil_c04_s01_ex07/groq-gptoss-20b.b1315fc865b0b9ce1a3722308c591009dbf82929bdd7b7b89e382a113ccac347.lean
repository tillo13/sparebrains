import Mathlib

open Set

/-- Mathematics in Lean, Chapter 4 §1 (Sets), exercise 7. Avigad & Massot, Apache-2.0, commit dd6d752. -/
theorem mil_c04_s01_ex07 {α : Type*} (s t : Set α) : s \ t ∪ t \ s = (s ∪ t) \ (s ∩ t) := by
  ext x
  constructor
  · intro hx
    rcases hx with hx | hx
    · rcases hx with ⟨hx_s, hx_not_t⟩
      refine ⟨?_, ?_⟩
      · exact Or.inl hx_s
      · intro h
        exact hx_not_t h.2
    · rcases hx with ⟨hx_t, hx_not_s⟩
      refine ⟨?_, ?_⟩
      · exact Or.inr hx_t
      · intro h
        exact hx_not_s h.1
  · intro hx
    rcases hx with ⟨hx_union, hx_not_inter⟩
    rcases hx_union with hx_s | hx_t
    · have hx_not_t : x ∉ t := by
        intro h_t
        exact hx_not_inter ⟨hx_s, h_t⟩
      exact Or.inl ⟨hx_s, hx_not_t⟩
    · have hx_not_s : x ∉ s := by
        intro h_s
        exact hx_not_inter ⟨h_s, hx_t⟩
      exact Or.inr ⟨hx_t, hx_not_s⟩
