import Mathlib

open scoped Nat
open scoped Real

/-- Consider the function $f(x)=5x+4$.  What is $f(1)$? -/
theorem mathd_algebra_171 (f : ℝ → ℝ) (h₀ : ∀ x, f x = 5 * x + 4) : f 1 = 9 := by
  have h1 := h₀ 1
  rw [show (5 : ℝ) * 1 + 4 = 9 by norm_num] at h1
  exact h1
