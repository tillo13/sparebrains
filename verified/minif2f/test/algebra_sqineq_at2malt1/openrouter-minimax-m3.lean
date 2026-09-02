import Mathlib

open scoped Nat
open scoped Real

theorem algebra_sqineq_at2malt1 (a : ℝ) : a * (2 - a) ≤ 1 := by
  have h : 0 ≤ (1 - a) ^ 2 := sq_nonneg (1 - a)
  have h1 : (1 - a) ^ 2 = 1 - 2 * a + a * a := by ring
  have h2 : a * (2 - a) = 2 * a - a * a := by ring
  have h3 : 1 - a * (2 - a) = (1 - a) ^ 2 := by
    rw [h2, h1]
    ring
  linarith [h, h3]
