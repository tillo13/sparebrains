import Mathlib

open scoped Nat
open scoped Real

theorem algebra_sqineq_at2malt1 (a : ℝ) : a * (2 - a) ≤ 1 := by
  have h : 0 ≤ 1 - a * (2 - a) := by
    have h1 : 1 - a * (2 - a) = (a - 1) ^ 2 := by ring
    rw [h1]
    exact sq_nonneg (a - 1)
  linarith
