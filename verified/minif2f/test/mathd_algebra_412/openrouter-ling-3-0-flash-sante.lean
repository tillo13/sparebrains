import Mathlib

open scoped Nat
open scoped Real

/--
The sum of two numbers is 25 and their difference is 11. What is the larger of the two numbers? -/
theorem mathd_algebra_412 (x y : ℝ) (h₀ : x + y = 25) (h₁ : x - y = 11) : x = 18 := by
  have h₂ : (x + y) + (x - y) = 25 + 11 := by rw [h₀, h₁]
  ring_nf at h₂
  linarith
