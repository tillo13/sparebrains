import Mathlib

open Function
open Set

/-- Mathematics in Lean, Chapter 4 §2 (Functions), exercise 3. Avigad & Massot, Apache-2.0, commit dd6d752. -/
theorem mil_c04_s02_ex03 {α β : Type*} (f : α → β) (u : Set β) : f '' (f ⁻¹' u) ⊆ u := by
  have h_main : f '' (f ⁻¹' u) ⊆ u := by
    intro y hy
    -- Assume y is in the image of the preimage of u under f
    rcases hy with ⟨x, hx, rfl⟩
    -- Obtain x such that x is in the preimage of u and f x = y
    have hx' : f x ∈ u := hx
    -- Since x is in the preimage of u, f x is in u
    exact hx'
    -- Therefore, y = f x is in u
  
  exact h_main
