import Mathlib

open scoped Nat
open scoped Real

/-- What is the value of $\sqrt{1,\!000,\!000} - \sqrt[3]{1,\!000,\!000}$? -/
theorem mathd_algebra_208 : Real.sqrt 1000000 - 1000000 ^ ((1 : ℝ) / 3) = 900 := by
  rw [Real.sqrt_eq_rpow]
  -- Now we have 1000000 ^ (1/2) - 1000000 ^ (1/3) = 900
  -- We need to show 1000000 ^ (1/2) = 1000 and 1000000 ^ (1/3) = 100.
  -- We can use `norm_num` on each term separately.
  norm_num
