import Mathlib

open Function
open Set

/-- Mathematics in Lean, Chapter 4 §2 (Functions), exercise 7. Avigad & Massot, Apache-2.0, commit dd6d752. -/
theorem mil_c04_s02_ex07 {α β : Type*} (f : α → β) (u v : Set β) : f ⁻¹' (u ∪ v) = f ⁻¹' u ∪ f ⁻¹' v := by
  ext x
  constructor
  · intro h
    simp only [mem_preimage, mem_union] at *
    cases h with
    | inl h => left; assumption
    | inr h => right; assumption
  · intro h
    simp only [mem_preimage, mem_union] at *
    cases h with
    | inl h => left; assumption
    | inr h => right; assumption
