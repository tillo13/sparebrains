import Mathlib

open scoped Nat
open scoped Real

/-- If $a = 8$, what is the value of $\left(16\sqrt[3]{a^2}\right)^{\frac 13}$? -/
theorem mathd_algebra_114 (a : ℝ) (h₀ : a = 8) :
    (16 * (a ^ 2) ^ ((1 : ℝ) / 3)) ^ ((1 : ℝ) / 3) = 4 := by
  rw [h₀]
  -- (16 * (8^2)^(1/3))^(1/3) = 4
  -- = (16 * 4)^(1/3) = 64^(1/3) = 4
  -- Let's prove this step by step
  have h1 : (8 : ℝ) ^ 2 = 64 := by norm_num
  rw [h1]
  have h2 : (64 : ℝ) ^ ((1 : ℝ) / 3) = 4 := by norm_num
  rw [h2]
  have h3 : (16 * 4 : ℝ) ^ ((1 : ℝ) / 3) = 4 := by norm_num
  rw [h3]
