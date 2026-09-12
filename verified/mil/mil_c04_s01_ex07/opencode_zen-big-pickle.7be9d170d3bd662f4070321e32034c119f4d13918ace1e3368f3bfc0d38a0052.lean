import Mathlib

open Set

/-- Mathematics in Lean, Chapter 4 §1 (Sets), exercise 7. Avigad & Massot, Apache-2.0, commit dd6d752. -/
theorem mil_c04_s01_ex07 {α : Type*} (s t : Set α) : s \ t ∪ t \ s = (s ∪ t) \ (s ∩ t) := by
  ext x
  constructor
  · rintro (h | h)
    · constructor
      · exact Or.inl h.1
      · intro hx
        exact h.2 hx.2
    · constructor
      · exact Or.inr h.1
      · intro hx
        exact h.2 hx.1
  · rintro ⟨hxst, hxnot⟩
    rcases hxst with hxs | hxt
    · left
      exact ⟨hxs, fun hxt => hxnot ⟨hxs, hxt⟩⟩
    · right
      exact ⟨hxt, fun hxs => hxnot ⟨hxs, hxt⟩⟩
