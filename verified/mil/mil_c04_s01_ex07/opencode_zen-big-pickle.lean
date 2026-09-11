import Mathlib

open Set

/-- Mathematics in Lean, Chapter 4 §1 (Sets), exercise 7. Avigad & Massot, Apache-2.0, commit dd6d752. -/
theorem mil_c04_s01_ex07 {α : Type*} (s t : Set α) : s \ t ∪ t \ s = (s ∪ t) \ (s ∩ t) := by
  ext x
  constructor
  · intro h
    rcases h with hst | hts
    · rcases hst with ⟨hs, hnt⟩
      constructor
      · left
        exact hs
      · intro hst_int
        rcases hst_int with ⟨hs', ht'⟩
        exact hnt ht'
    · rcases hts with ⟨ht, hns⟩
      constructor
      · right
        exact ht
      · intro hst_int
        rcases hst_int with ⟨hs', ht'⟩
        exact hns hs'
  · intro h
    rcases h with ⟨hunion, hnot_inter⟩
    rcases hunion with hs | ht
    · left
      constructor
      · exact hs
      · intro ht'
        apply hnot_inter
        exact ⟨hs, ht'⟩
    · right
      constructor
      · exact ht
      · intro hs'
        apply hnot_inter
        exact ⟨hs', ht⟩
