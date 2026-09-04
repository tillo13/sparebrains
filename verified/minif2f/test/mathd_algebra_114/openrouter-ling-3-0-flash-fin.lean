import Mathlib

open scoped Nat
open scoped Real

/-- If $a = 8$, what is the value of $\left(16\sqrt[3]{a^2}\right)^{\frac 13}$? -/
theorem mathd_algebra_114 (a : ℝ) (h₀ : a = 8) :
    (16 * (a ^ 2) ^ ((1 : ℝ) / 3)) ^ ((1 : ℝ) / 3) = 4 := by
  rw [h₀]
  -- Now we need to simplify (16 * (8 ^ 2) ^ (1/3)) ^ (1/3) = 4
  -- Let's use the fact that 8 = 2^3
  -- Actually, let me try a different approach
  have h1 : (8 : ℝ) ^ 2 = 64 := by norm_num
  rw [h1]
  -- (16 * 64 ^ (1/3)) ^ (1/3) = 4
  have h2 : (64 : ℝ) ^ ((1 : ℝ) / 3) = 4 := by norm_num
  rw [h2]
  -- (16 * 4) ^ (1/3) = 4
  -- 16 * 4 = 64
  have h3 : (16 : ℝ) * 4 = 64 := by norm_num
  rw [h3]
  -- 64 ^ (1/3) = 4
  norm_num
