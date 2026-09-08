import Mathlib

open scoped Nat
open scoped Real

/-- Find the radius of the circle with equation $x^2 + 8x + y^2 - 6y = 0$. -/
theorem mathd_algebra_107 (x y : ℝ) (h₀ : x ^ 2 + 8 * x + y ^ 2 - 6 * y = 0) :
    (x + 4) ^ 2 + (y - 3) ^ 2 = 5 ^ 2 := by
  rw [pow_two, pow_two] at h₀
  -- h₀ : x * x + 8 * x + y * y - 6 * y = 0
  -- Goal: (x + 4) ^ 2 + (y - 3) ^ 2 = 25
  ring_nf at h₀
  -- h₀ : x * x + 8 * x + y * y - 6 * y = 0
  -- Goal: x * x + 8 * x + 16 + y * y - 6 * y + 9 = 25
  -- Actually ring_nf on goal:
  ring_nf
  -- Goal: x * x + 8 * x + y * y - 6 * y + 25 = 25
  -- Then linarith?
  linarith
