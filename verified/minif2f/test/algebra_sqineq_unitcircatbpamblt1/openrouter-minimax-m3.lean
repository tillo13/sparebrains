import Mathlib

open scoped Nat
open scoped Real

theorem algebra_sqineq_unitcircatbpamblt1 (a b : ℝ) (h₀ : a ^ 2 + b ^ 2 = 1) :
    a * b + (a - b) ≤ 1 := by
  have h1 : 0 ≤ (1 - a) ^ 2 := sq_nonneg (1 - a)
  have h2 : 0 ≤ (1 - b) ^ 2 := sq_nonneg (1 - b)
  have h3 : 0 ≤ (a + b) ^ 2 := sq_nonneg (a + b)
  nlinarith [h₀, h1, h2, h3]
