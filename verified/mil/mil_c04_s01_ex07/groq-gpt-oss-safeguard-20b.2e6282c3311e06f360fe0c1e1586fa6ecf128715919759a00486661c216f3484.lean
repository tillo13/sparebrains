import Mathlib

open Set

/-- Mathematics in Lean, Chapter 4 §1 (Sets), exercise 7. Avigad & Massot, Apache-2.0, commit dd6d752. -/
theorem mil_c04_s01_ex07 {α : Type*} (s t : Set α) : s \ t ∪ t \ s = (s ∪ t) \ (s ∩ t) := by
  ext x
  constructor
  · intro hx
    rcases hx with hx | hx
    · rcases hx with ⟨hs, hnt⟩
      refine ⟨?_, ?_⟩
      · exact Or.inl hs
      · intro h
        rcases h with ⟨hs', ht'⟩
        exact hnt ht'
    · rcases hx with ⟨ht, hns⟩
      refine ⟨?_, ?_⟩
      · exact Or.inr ht
      · intro h
        rcases h with ⟨hs', ht'⟩
        exact hns hs'
  · intro hx
    rcases hx with ⟨hmem, hnot⟩
    rcases hmem with hs | ht
    · have hnot_t : x ∉ t := by
        intro hxt
        exact hnot ⟨hs, hxt⟩
      exact Or.inl ⟨hs, hnot_t⟩
    · have hnot_s : x ∉ s := by
        intro hxs
        exact hnot ⟨hxs, ht⟩
      exact Or.inr ⟨ht, hnot_s⟩
