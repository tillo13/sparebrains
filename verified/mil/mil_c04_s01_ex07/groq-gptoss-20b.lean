import Mathlib

open Set

/-- Mathematics in Lean, Chapter 4 §1 (Sets), exercise 7. Avigad & Massot, Apache-2.0, commit dd6d752. -/
theorem mil_c04_s01_ex07 {α : Type*} (s t : Set α) : s \ t ∪ t \ s = (s ∪ t) \ (s ∩ t) := by
  classical
  ext x
  constructor
  · intro hx
    rcases hx with hx | hx
    · -- hx : x ∈ s \ t
      rcases hx with ⟨hs, hnt⟩
      have hmem : x ∈ s ∪ t := Or.inl hs
      have hnot : x ∉ s ∩ t := by
        intro hst
        exact hnt hst.2
      exact ⟨hmem, hnot⟩
    · -- hx : x ∈ t \ s
      rcases hx with ⟨ht, hns⟩
      have hmem : x ∈ s ∪ t := Or.inr ht
      have hnot : x ∉ s ∩ t := by
        intro hst
        exact hns hst.1
      exact ⟨hmem, hnot⟩
  · intro hx
    rcases hx with ⟨hmem, hnot⟩
    rcases hmem with hs | ht
    · -- hs : x ∈ s
      have hnt : x ∉ t := by
        intro ht'
        apply hnot
        exact And.intro hs ht'
      exact Or.inl ⟨hs, hnt⟩
    · -- ht : x ∈ t
      have hns : x ∉ s := by
        intro hs'
        apply hnot
        exact And.intro hs' ht
      exact Or.inr ⟨ht, hns⟩
