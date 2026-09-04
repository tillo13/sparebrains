import Mathlib

open scoped Nat
open scoped Real

/-- Five plus $500\%$ of $10$ is the same as $110\%$ of what number? -/
theorem mathd_algebra_400 (x : ℝ) (h₀ : 5 + 500 / 100 * 10 = 110 / 100 * x) : x = 50 := by
  have h₁ : 110 / 100 * x = 5 + 500 / 100 * 10 := by
    linarith
  have h₂ : 110 / 100 * x = 55 := by
    linarith
  have h₃ : x = 55 * (100 / 110) := by
    linarith
  have h₄ : x = 50 := by
    linarith
  exact h₄
