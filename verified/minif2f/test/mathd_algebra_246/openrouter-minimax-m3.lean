import Mathlib

open scoped Nat
open scoped Real

/-- If $f(x)=ax^4-bx^2+x+5$ and $f(-3)=2,$ then what is the value of $f(3)$? -/
theorem mathd_algebra_246 (a b : ℝ) (f : ℝ → ℝ) (h₀ : ∀ x, f x = a * x ^ 4 - b * x ^ 2 + x + 5)
    (h₂ : f (-3) = 2) : f 3 = 8 := by
  have hn3 : f (-3) = a * (-3) ^ 4 - b * (-3) ^ 2 + (-3) + 5 := h₀ (-3)
  have h3 : f 3 = a * 3 ^ 4 - b * 3 ^ 2 + 3 + 5 := h₀ 3
  rw [hn3] at h₂
  rw [show (-3 : ℝ) ^ 4 = 3 ^ 4 from by norm_num,
      show (-3 : ℝ) ^ 2 = 3 ^ 2 from by norm_num] at h₂
  have key : a * 3 ^ 4 - b * 3 ^ 2 + 3 + 5 = (a * 3 ^ 4 - b * 3 ^ 2 + (-3) + 5) + 6 := by ring
  rw [h3, key]
  rw [h₂]
  ring
