import Mathlib

open Function
open Set

/-- Mathematics in Lean, Chapter 4 §2 (Functions), exercise 1. Avigad & Massot, Apache-2.0, commit dd6d752. -/
theorem mil_c04_s02_ex01 {α β : Type*} (f : α → β) (s : Set α) (v : Set β) : f '' s ⊆ v ↔ s ⊆ f ⁻¹' v := by
  constructor
  · intro h x hx
    have h1 : f x ∈ f '' s := by
      simp only [mem_image]
      exact ⟨x, hx, rfl⟩
    have h2 : f x ∈ v := h h1
    simp only [mem_preimage, mem_setOf_eq] at h2 ⊢
    exact h2
  · intro h y hy
    rcases hy with ⟨x, hx, rfl⟩
    have h1 : x ∈ s := hx
    have h2 : x ∈ f ⁻¹' v := h h1
    simp only [mem_preimage, mem_setOf_eq] at h2 ⊢
    exact h2
