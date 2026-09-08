import Mathlib

open Set

/-- Mathematics in Lean, Chapter 4 §1 (Sets), exercise 7. Avigad & Massot, Apache-2.0, commit dd6d752. -/
theorem mil_c04_s01_ex07 {α : Type*} (s t : Set α) : s \ t ∪ t \ s = (s ∪ t) \ (s ∩ t) := by
  ext x
  constructor
  · intro h
    cases h with
    | inl h =>
      cases h with
      | intro hst hnst =>
      exact ⟨Or.inl hst, fun h' => hnst (And.right h')⟩
    | inr h =>
      cases h with
      | intro hts hnts =>
      exact ⟨Or.inr hts, fun h' => hnts (And.left h')⟩
  · intro h
    cases h with
    | intro h hn =>
      cases h with
      | inl hs =>
        exact Or.inl ⟨hs, fun h' => hn (And.intro hs h')⟩
      | inr ht =>
        exact Or.inr ⟨ht, fun h' => hn (And.intro h' ht)⟩
