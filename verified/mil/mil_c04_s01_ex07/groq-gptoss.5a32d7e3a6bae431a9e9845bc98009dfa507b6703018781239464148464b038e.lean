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
      · intro hst
        rcases hst with ⟨_, ht⟩
        exact hnt ht
    · rcases hx with ⟨ht, hns⟩
      refine ⟨?_, ?_⟩
      · exact Or.inr ht
      · intro hst
        rcases hst with ⟨hs, _⟩
        exact hns hs
  · intro hx
    rcases hx with ⟨hU, hN⟩
    cases hU with
    | inl hs =>
        have hnt : x ∉ t := by
          intro ht
          apply hN
          exact ⟨hs, ht⟩
        exact Or.inl ⟨hs, hnt⟩
    | inr ht =>
        have hns : x ∉ s := by
          intro hs
          apply hN
          exact ⟨hs, ht⟩
        exact Or.inr ⟨ht, hns⟩
