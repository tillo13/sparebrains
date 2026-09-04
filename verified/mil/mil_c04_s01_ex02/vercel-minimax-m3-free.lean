import Mathlib

open Set

/-- Mathematics in Lean, Chapter 4 §1 (Sets), exercise 2. Avigad & Massot, Apache-2.0, commit dd6d752. -/
theorem mil_c04_s01_ex02 {α : Type*} (s t u : Set α) : s \ (t ∪ u) ⊆ (s \ t) \ u := by
  intro x hx
  have hxs : x ∈ s := hx.1
  have hxnt : ¬ x ∈ t ∪ u := hx.2
  have hxnu : x ∉ u := fun hxu => hxnt (Or.inr hxu)
  have hxnt' : x ∉ t := fun hxt => hxnt (Or.inl hxt)
  exact ⟨⟨hxs, hxnt'⟩, hxnu⟩
