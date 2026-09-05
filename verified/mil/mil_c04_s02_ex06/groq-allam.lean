import Mathlib

open Function
open Set

/-- Mathematics in Lean, Chapter 4 §2 (Functions), exercise 6. Avigad & Massot, Apache-2.0, commit dd6d752. -/
theorem mil_c04_s02_ex06 {α β : Type*} (f : α → β) (u v : Set β) (h : u ⊆ v) : f ⁻¹' u ⊆ f ⁻¹' v := by
  -- To prove that f ⁻¹' u is a subset of f ⁻¹' v, we take an arbitrary element
  -- `x` from f ⁻¹' u and show that it must be in f ⁻¹' v.
  intro x
  -- Assume `x` is in the preimage of `u`.
  intro hx
  -- By the definition of preimage (`Set.mem_preimage`), `x ∈ f ⁻¹' u` means `f x ∈ u`.
  rw [mem_preimage] at hx
  -- We are given the hypothesis `h : u ⊆ v`. This means that any element in `u` is also in `v`.
  -- Since `f x ∈ u` (from `hx`) and `u ⊆ v` (from `h`), it follows that `f x ∈ v`.
  have fx_in_v : f x ∈ v := h hx
  -- The goal is to show `x ∈ f ⁻¹' v`.
  -- By the definition of preimage, `x ∈ f ⁻¹' v` means `f x ∈ v`.
  -- This is exactly what we have in `fx_in_v`.
  exact fx_in_v
