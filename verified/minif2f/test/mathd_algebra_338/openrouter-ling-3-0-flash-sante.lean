import Mathlib

open scoped Nat
open scoped Real

/-- If $3a + b + c = -3, a+3b+c = 9, a+b+3c = 19$, then find $abc$. -/
theorem mathd_algebra_338 (a b c : ℝ) (h₀ : 3 * a + b + c = -3) (h₁ : a + 3 * b + c = 9)
    (h₂ : a + b + 3 * c = 19) : a * b * c = -56 := by
  have h₃ : (3 * a + b + c) - (a + 3 * b + c) = -3 - 9 := by rw [h₀, h₁]
  have h₄ : (a + b + 3 * c) - (a + 3 * b + c) = 19 - 9 := by rw [h₂, h₁]
  have h₅ : a = b - 6 := by linarith [h₃]
  have h₆ : c = b + 5 := by linarith [h₄]
  have h₇ : (b - 6) + 3 * b + (b + 5) = 9 := by
    rw [h₅, h₆] at h₁
    exact h₁
  have h₈ : b = 2 := by linarith [h₇]
  have h₉ : a = -4 := by
    rw [h₅, h₈]
    norm_num
  have h₁₀ : c = 7 := by
    rw [h₆, h₈]
    norm_num
  rw [h₉, h₈, h₁₀]
  norm_num
