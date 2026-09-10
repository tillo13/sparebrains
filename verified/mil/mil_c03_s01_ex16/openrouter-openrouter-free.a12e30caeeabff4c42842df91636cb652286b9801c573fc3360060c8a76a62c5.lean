import Mathlib

open Function

/-- Mathematics in Lean, Chapter 3 §1 (Implication and the Universal Quantifier), exercise 16. Avigad & Massot, Apache-2.0, commit dd6d752. -/
theorem mil_c03_s01_ex16 {c : ℝ} (h : c ≠ 0) : Injective fun x ↦ c * x := by
  have h_main : Injective (fun x : ℝ => c * x) := by
    intro x y hxy
    -- Use the cancellation property of multiplication by a non-zero scalar
    have h₁ : c * x = c * y := hxy
    have h₂ : x = y := by
      apply mul_left_cancel₀ h
      linarith
    exact h₂
  exact h_main
