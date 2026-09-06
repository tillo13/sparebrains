import Mathlib

open scoped Nat
open scoped Real

theorem algebra_sqineq_unitcircatbpamblt1 (a b : ℝ) (h₀ : a ^ 2 + b ^ 2 = 1) :
    a * b + (a - b) ≤ 1 := by
  have ha : a ≤ 1 := by nlinarith [sq_nonneg (a - 1), sq_nonneg b, h₀]
  have hb : b ≥ -1 := by nlinarith [sq_nonneg (b + 1), sq_nonneg a, h₀]
  have h1 : a - 1 ≤ 0 := by linarith
  have h2 : b + 1 ≥ 0 := by linarith
  have h3 : (a - 1) * (b + 1) ≤ 0 := by
    have h : 0 ≤ (1 - a) * (b + 1) := mul_nonneg (by linarith) (by linarith)
    linarith [show (1 - a) * (b + 1) = -((a - 1) * (b + 1)) by ring]
  linarith [show a * b + (a - b) = (a - 1) * (b + 1) + 1 by ring]
