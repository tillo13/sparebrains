import Mathlib

open scoped Nat
open scoped Real

/--
Jasmine drank 1.5 pints of water on the first 3 miles of her hike. If she continued at this rate, how many pints of water would she drink in the next 10 miles? -/
theorem mathd_algebra_440 (x : ℝ) (h₀ : 3 / 2 / 3 = x / 10) : x = 5 := by
  have h₁ : (3 / 2 / 3 : ℝ) = 1 / 2 := by norm_num
  rw [h₁] at h₀
  have h₂ : (10 : ℝ) * (1 / 2) = 5 := by norm_num
  linarith
