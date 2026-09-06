import Mathlib

open scoped Nat
open scoped Real

/--
The sum of two numbers is 25 and their difference is 11. What is the larger of the two numbers? -/
theorem mathd_algebra_412 (x y : ℝ) (h₀ : x + y = 25) (h₁ : x - y = 11) : x = 18 := by
  have h₂ : 2 * x = 36 := by
    calc 2 * x = (x + y) + (x - y) := by ring
      _ = 25 + 11 := by rw [h₀, h₁]
      _ = 36 := by ring
  have h₃ : x = 18 := by
    calc x = (2 * x) / 2 := by field_simp [two_ne_zero]
      _ = 36 / 2 := by rw [h₂]
      _ = 18 := by norm_num
  exact h₃
