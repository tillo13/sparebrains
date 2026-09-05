import Mathlib

open Function
open Set

/-- Mathematics in Lean, Chapter 4 §2 (Functions), exercise 3. Avigad & Massot, Apache-2.0, commit dd6d752. -/
theorem mil_c04_s02_ex03 {α β : Type*} (f : α → β) (u : Set β) : f '' (f ⁻¹' u) ⊆ u := by
  intro y h
  obtain ⟨x, hx1, hx2⟩ := h
  exact hx2 ▸ hx1
