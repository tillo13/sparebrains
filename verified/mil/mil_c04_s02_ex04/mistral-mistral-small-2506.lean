import Mathlib

open Function
open Set

/-- Mathematics in Lean, Chapter 4 §2 (Functions), exercise 4. Avigad & Massot, Apache-2.0, commit dd6d752. -/
theorem mil_c04_s02_ex04 {α β : Type*} (f : α → β) (u : Set β) (h : Surjective f) : u ⊆ f '' (f ⁻¹' u) := by
  intro x hx
  obtain ⟨y, hy⟩ := h x
  have : y ∈ f ⁻¹' u := by
    simp only [mem_preimage]
    exact hy ▸ hx
  simp only [mem_image]
  exact ⟨y, this, hy⟩
