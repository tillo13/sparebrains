import Mathlib

open scoped Nat
open scoped Real

/-- If $f(x)=ax^4-bx^2+x+5$ and $f(-3)=2,$ then what is the value of $f(3)$? -/
theorem mathd_algebra_246 (a b : ℝ) (f : ℝ → ℝ) (h₀ : ∀ x, f x = a * x ^ 4 - b * x ^ 2 + x + 5)
    (h₂ : f (-3) = 2) : f 3 = 8 := by
  have h₃ : f 3 = a * 3 ^ 4 - b * 3 ^ 2 + 3 + 5 := h₀ 3
  have h₄ : f (-3) = a * (-3) ^ 4 - b * (-3) ^ 2 + (-3) + 5 := h₀ (-3)
  rw [h₄] at h₂
  have h₅ : a * (-3 : ℝ) ^ 4 = a * 81 := by ring
  have h₆ : b * (-3 : ℝ) ^ 2 = b * 9 := by ring
  rw [h₅, h₆] at h₂
  -- h₂ : a * 81 - b * 9 + (-3) + 5 = 2
  -- Simplify: a * 81 - b * 9 + 2 = 2, so a * 81 = b * 9
  have h₇ : a * 81 - b * 9 = 0 := by linarith
  -- Now f 3 = a * 81 - b * 9 + 3 + 5 = 0 + 3 + 5 = 8
  rw [h₃]
  linarith
