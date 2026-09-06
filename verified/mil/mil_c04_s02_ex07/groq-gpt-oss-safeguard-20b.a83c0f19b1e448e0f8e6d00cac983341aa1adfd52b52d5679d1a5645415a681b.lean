import Mathlib

open Function
open Set

/-- Mathematics in Lean, Chapter 4 §2 (Functions), exercise 7. Avigad & Massot, Apache-2.0, commit dd6d752. -/
theorem mil_c04_s02_ex07 {α β : Type*} (f : α → β) (u v : Set β) : f ⁻¹' (u ∪ v) = f ⁻¹' u ∪ f ⁻¹' v := by
  ext x
  constructor
  · intro hx
    have hx' : f x ∈ u ∪ v := by
      simpa using hx
    rcases hx' with hx' | hx'
    · left
      simpa using hx'
    · right
      simpa using hx'
  · intro hx
    rcases hx with hx | hx
    · have : f x ∈ u := by
        simpa using hx
      have : f x ∈ u ∪ v := Or.inl this
      simpa using this
    · have : f x ∈ v := by
        simpa using hx
      have : f x ∈ u ∪ v := Or.inr this
      simpa using this
