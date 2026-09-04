import Mathlib

open Function
open Set

/-- Mathematics in Lean, Chapter 4 §2 (Functions), exercise 7. Avigad & Massot, Apache-2.0, commit dd6d752. -/
theorem mil_c04_s02_ex07 {α β : Type*} (f : α → β) (u v : Set β) : f ⁻¹' (u ∪ v) = f ⁻¹' u ∪ f ⁻¹' v := by
  ext x
  constructor
  · intro h
    rcases h with hu | hv
    · exact Or.inl hu
    · exact Or.inr hv
  · intro h
    rcases h with h1 | h2
    · exact Or.inl h1
    · exact Or.inr h2
