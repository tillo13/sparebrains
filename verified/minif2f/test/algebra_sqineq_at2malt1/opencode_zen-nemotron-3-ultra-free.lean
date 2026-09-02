import Mathlib

open scoped Nat
open scoped Real

theorem algebra_sqineq_at2malt1 (a : ℝ) : a * (2 - a) ≤ 1 := by
  have h_main : a * (2 - a) ≤ 1 := by
    have h₁ : a * (2 - a) = 2 * a - a ^ 2 := by
      ring
    rw [h₁]
    have h₂ : (a - 1) ^ 2 ≥ 0 := by nlinarith
    nlinarith [sq_nonneg (a - 1)]
  
  exact h_main
