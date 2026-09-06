import Mathlib

open Set

/-- Mathematics in Lean, Chapter 4 §1 (Sets), exercise 7. Avigad & Massot, Apache-2.0, commit dd6d752. -/
theorem mil_c04_s01_ex07 {α : Type*} (s t : Set α) : s \ t ∪ t \ s = (s ∪ t) \ (s ∩ t) := by
  ext x
  constructor
  · intro hx
    rcases hx with hx | hx
    · rcases hx with ⟨hs, hnt⟩
      exact ⟨Or.inl hs, by
        intro hst
        exact hnt hst.2⟩
    · rcases hx with ⟨ht, hns⟩
      exact ⟨Or.inr ht, by
        intro hst
        exact hns hst.1⟩
  · intro hx
    rcases hx with ⟨hmem, hnot⟩
    rcases hmem with hs | ht
    · have hnt : x ∉ t := by
        intro ht
        apply hnot
        exact And.intro hs ht
      exact Or.inl ⟨hs, hnt⟩
    · have hns : x ∉ s := by
        intro hs
        apply hnot
        exact And.intro hs ht
      exact Or.inr ⟨ht, hns⟩
