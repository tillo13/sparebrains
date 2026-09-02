import Mathlib

open scoped Nat
open scoped Real

theorem algebra_sqineq_at2malt1 (a : ℝ) : a * (2 - a) ≤ 1 := by
  have h_main : a * (2 - a) ≤ 1 := by
    have h₁ : (a - 1) ^ 2 ≥ 0 := by nlinarith
    -- Expand and rearrange the inequality to match the square form
    have h₂ : a * (2 - a) = 1 - (a - 1) ^ 2 := by
      ring_nf
      <;>
      linarith
    -- Use the fact that the square is non-negative to prove the inequality
    rw [h₂]
    nlinarith
  exact h_main
