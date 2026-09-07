import Mathlib

open scoped Nat
open scoped Real

/-- Find the radius of the circle with equation $x^2 + 8x + y^2 - 6y = 0$. -/
theorem mathd_algebra_107 (x y : ℝ) (h₀ : x ^ 2 + 8 * x + y ^ 2 - 6 * y = 0) :
    (x + 4) ^ 2 + (y - 3) ^ 2 = 5 ^ 2 := by
  rw [show (x + 4) ^ 2 + (y - 3) ^ 2 = (x ^ 2 + 8 * x + y ^ 2 - 6 * y) + 25 from by ring,
      h₀, zero_add]
  norm_num
