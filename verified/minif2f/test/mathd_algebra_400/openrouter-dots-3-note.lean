import Mathlib

open scoped Nat
open scoped Real

/-- Five plus $500\%$ of $10$ is the same as $110\%$ of what number? -/
theorem mathd_algebra_400 (x : ℝ) (h₀ : 5 + 500 / 100 * 10 = 110 / 100 * x) : x = 50 := by
  have h1 : (5 + 500 / 100 * 10 : ℝ) = 55 := by norm_num
  have h2 : (110 / 100 : ℝ) = 11 / 10 := by norm_num
  rw [h1, h2] at h₀
  -- h₀ : 55 = (11 / 10) * x
  field_simp at h₀
  -- h₀ : x * 11 = 55 * 10? Actually field_simp might give something else.
  -- Let's see: field_simp at h₀ will clear denominators in h₀.
  -- h₀ : 55 = (11/10)*x => multiply both sides by 10: 550 = 11*x => x = 50.
  -- We can use linarith or field_simp then nlinarith.
  nlinarith
