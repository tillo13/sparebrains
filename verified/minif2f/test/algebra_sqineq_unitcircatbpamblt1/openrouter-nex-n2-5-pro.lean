import Mathlib

open scoped Nat
open scoped Real

theorem algebra_sqineq_unitcircatbpamblt1 (a b : ℝ) (h₀ : a ^ 2 + b ^ 2 = 1) :
    a * b + (a - b) ≤ 1 := by
  have h₁ : a ≤ 1 := by
    nlinarith [sq_nonneg (a - 1), sq_nonneg b]
  have h₂ : -1 ≤ b := by
    nlinarith [sq_nonneg (b + 1), sq_nonneg a]
  have h₃ : (a - 1) * (b + 1) ≤ 0 := by
    apply mul_nonpos_of_nonpos_of_nonneg
    · linarith
    · linarith
  have h₄ : a * b + (a - b) = 1 + (a - 1) * (b + 1) := by
    ring
  rw [h₄]
  linarith
