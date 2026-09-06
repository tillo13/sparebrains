import Mathlib

open scoped Nat
open scoped Real

theorem algebra_sqineq_at2malt1 (a : ℝ) : a * (2 - a) ≤ 1 := by
  have h : 0 ≤ 1 - a * (2 - a) := by
    ring_nf
    nlinarith [sq_nonneg (a - 1)]
  linarith
