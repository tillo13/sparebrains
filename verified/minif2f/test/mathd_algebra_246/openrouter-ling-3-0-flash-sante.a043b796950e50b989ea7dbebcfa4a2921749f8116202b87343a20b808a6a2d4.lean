import Mathlib

open scoped Nat
open scoped Real

/-- If $f(x)=ax^4-bx^2+x+5$ and $f(-3)=2,$ then what is the value of $f(3)$? -/
theorem mathd_algebra_246 (a b : ℝ) (f : ℝ → ℝ) (h₀ : ∀ x, f x = a * x ^ 4 - b * x ^ 2 + x + 5)
    (h₂ : f (-3) = 2) : f 3 = 8 := by
  have h1 : f 3 = a * 3 ^ 4 - b * 3 ^ 2 + 3 + 5 := by rw [h₀ 3]
  have h2 : f (-3) = a * (-3) ^ 4 - b * (-3) ^ 2 + (-3) + 5 := by rw [h₀ (-3)]
  rw [h2] at h₂
  -- Now h₂ : a * (-3) ^ 4 - b * (-3) ^ 2 + (-3) + 5 = 2
  -- Simplify powers: (-3) ^ 4 = 81, (-3) ^ 2 = 9
  norm_num at h₂
  -- h₂ : 81 * a - 9 * b + 2 = 2
  -- So 81*a - 9*b = 0
  linarith
  -- Now we need to show f 3 = 8. We have h1 : f 3 = 81*a - 9*b + 8.
  -- We know 81*a - 9*b = 0 from linarith? Actually linarith solves goals like ... = ...
  -- Let's restructure.
