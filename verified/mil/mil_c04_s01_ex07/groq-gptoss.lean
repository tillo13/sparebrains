import Mathlib

open Set

/-- Mathematics in Lean, Chapter 4 §1 (Sets), exercise 7. Avigad & Massot, Apache-2.0, commit dd6d752. -/
theorem mil_c04_s01_ex07 {α : Type*} (s t : Set α) : s \ t ∪ t \ s = (s ∪ t) \ (s ∩ t) := by
  ext x
  constructor
  · intro hx
    rcases hx with hx | hx
    · rcases hx with ⟨hs, hnt⟩
      refine ⟨Or.inl hs, ?_⟩
      intro hst
      rcases hst with ⟨_, ht⟩
      exact hnt ht
    · rcases hx with ⟨ht, hns⟩
      refine ⟨Or.inr ht, ?_⟩
      intro hst
      rcases hst with ⟨hs, _⟩
      exact hns hs
  · intro hx
    rcases hx with ⟨hmem, hnot⟩
    rcases hmem with hmem | hmem
    · left
      have hnt : x ∉ t := by
        intro ht
        apply hnot
        exact ⟨hmem, ht⟩
      exact ⟨hmem, hnt⟩
    · right
      have hns : x ∉ s := by
        intro hs
        apply hnot
        exact ⟨hs, hmem⟩
      exact ⟨hmem, hns⟩
