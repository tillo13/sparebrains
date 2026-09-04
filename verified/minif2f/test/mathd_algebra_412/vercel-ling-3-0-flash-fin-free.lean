import Mathlib

open scoped Nat
open scoped Real

/--
The sum of two numbers is 25 and their difference is 11. What is the larger of the two numbers? -/
theorem mathd_algebra_412 (x y : ℝ) (h₀ : x + y = 25) (h₁ : x - y = 11) : x = 18 := by
  have : x = (x + y + (x - y)) / 2 := by ring
  rw [this]
  rw [h₀, h₁]
  norm_num
