import Mathlib

open scoped Nat
open scoped Real

/-- Five plus $500\%$ of $10$ is the same as $110\%$ of what number? -/
theorem mathd_algebra_400 (x : ℝ) (h₀ : 5 + 500 / 100 * 10 = 110 / 100 * x) : x = 50 := by
  have h₁ : 500 / 100 * 10 = 50 := by norm_num
  have h₂ : 55 = 110 / 100 * x := by linarith [h₀, h₁]
  have h₃ : 110 * x = 5500 := by
    calc 110 * x = 100 * (110 / 100 * x) := by ring
      _ = 100 * 55 := by rw [h₂]
      _ = 5500 := by norm_num
  linarith
