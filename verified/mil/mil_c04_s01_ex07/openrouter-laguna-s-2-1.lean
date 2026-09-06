import Mathlib

open Set

/-- Mathematics in Lean, Chapter 4 §1 (Sets), exercise 7. Avigad & Massot, Apache-2.0, commit dd6d752. -/
theorem mil_c04_s01_ex07 {α : Type*} (s t : Set α) : s \ t ∪ t \ s = (s ∪ t) \ (s ∩ t) := by
  ext x
  constructor
  · intro h
    cases h with
    | inl h =>
      exact ⟨Or.inl h.1, fun h' => False.elim (h.2 h'.right)⟩
    | inr h =>
      exact ⟨Or.inr h.1, fun h' => False.elim (h.2 h'.left)⟩
  · intro h
    cases h with
    | intro h1 h2 =>
      cases h1 with
      | inl hs =>
        have h_not_t : x ∉ t := fun h' => h2 ⟨hs, h'⟩
        exact Or.inl ⟨hs, h_not_t⟩
      | inr ht =>
        have h_not_s : x ∉ s := fun h' => h2 ⟨h', ht⟩
        exact Or.inr ⟨ht, h_not_s⟩
