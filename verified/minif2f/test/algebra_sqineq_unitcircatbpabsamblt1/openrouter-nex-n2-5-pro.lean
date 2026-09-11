import Mathlib

open scoped Nat
open scoped Real

theorem algebra_sqineq_unitcircatbpabsamblt1 (a b : ℝ) (h₀ : a ^ 2 + b ^ 2 = 1) :
    a * b + ‖a - b‖ ≤ 1 := by
  have h₁ : (a - b) ^ 2 = 1 - 2 * (a * b) := by
    calc
      (a - b) ^ 2 = a ^ 2 + b ^ 2 - 2 * (a * b) := by ring
      _ = 1 - 2 * (a * b) := by rw [h₀]
  have h₂ : ‖a - b‖ ^ 2 = 1 - 2 * (a * b) := by
    calc
      ‖a - b‖ ^ 2 = (a - b) ^ 2 := by simp [sq_abs]
      _ = 1 - 2 * (a * b) := h₁
  have h₃ : a * b = (1 - ‖a - b‖ ^ 2) / 2 := by linarith
  rw [h₃]
  linarith [sq_nonneg (‖a - b‖ - 1)]
