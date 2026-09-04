import Mathlib

open scoped Nat
open scoped Real

/-- If $a = 8$, what is the value of $\left(16\sqrt[3]{a^2}\right)^{\frac 13}$? -/
theorem mathd_algebra_114 (a : ℝ) (h₀ : a = 8) :
    (16 * (a ^ 2) ^ ((1 : ℝ) / 3)) ^ ((1 : ℝ) / 3) = 4 := by
  rw [h₀]
  -- Now we need to evaluate (16 * (8^2)^(1/3))^(1/3)
  -- Let's use the fact that for positive reals, (x^a)^b = x^(a*b)
  -- and other rpow properties
  ring
