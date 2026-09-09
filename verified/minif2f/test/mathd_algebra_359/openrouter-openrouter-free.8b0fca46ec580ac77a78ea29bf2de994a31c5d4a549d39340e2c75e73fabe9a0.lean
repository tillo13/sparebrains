import Mathlib

open scoped Nat
open scoped Real

/-- What is the value of $y$ in the arithmetic sequence $y + 6$, $12$, $y$? -/
theorem mathd_algebra_359 (y : ℝ) (h₀ : y + 6 + y = 2 * 12) : y = 9 := by
  have h₁ : y + 6 + y = 24 := by
    norm_num at h₀ ⊢
    <;> linarith
  
  have h₂ : 2 * y + 6 = 24 := by
    have h₂₁ : y + 6 + y = 24 := h₁
    have h₂₂ : 2 * y + 6 = 24 := by
      ring_nf at h₂₁ ⊢
      linarith
    exact h₂₂
  
  have h₃ : 2 * y = 18 := by
    have h₃₁ : 2 * y + 6 = 24 := h₂
    have h₃₂ : 2 * y = 18 := by
      linarith
    exact h₃₂
  
  have h₄ : y = 9 := by
    have h₄₁ : 2 * y = 18 := h₃
    have h₄₂ : y = 9 := by
      apply mul_left_cancel₀ (show (2 : ℝ) ≠ 0 by norm_num)
      linarith
    exact h₄₂
  
  exact h₄
