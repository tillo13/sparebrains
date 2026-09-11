import Mathlib

open scoped Nat
open scoped Real

/-- Find $y$: $\sqrt{19+3y} = 7$. -/
theorem mathd_algebra_263 (y : ℝ) (h₀ : 0 ≤ 19 + 3 * y) (h₁ : Real.sqrt (19 + 3 * y) = 7) :
    y = 10 := by
  have h₂ : (Real.sqrt (19 + 3 * y)) ^ 2 = 7 ^ 2 := by
    rw [h₁]
    <;> norm_num
  
  have h₃ : (Real.sqrt (19 + 3 * y)) ^ 2 = 19 + 3 * y := by
    rw [Real.sq_sqrt] <;> linarith
  
  have h₄ : 19 + 3 * y = 7 ^ 2 := by
    have h₄₁ : (Real.sqrt (19 + 3 * y)) ^ 2 = 7 ^ 2 := h₂
    have h₄₂ : (Real.sqrt (19 + 3 * y)) ^ 2 = 19 + 3 * y := h₃
    linarith
  
  have h₅ : 19 + 3 * y = 49 := by
    norm_num at h₄ ⊢
    <;> linarith
  
  have h₆ : 3 * y = 30 := by
    have h₆₁ : 19 + 3 * y = 49 := h₅
    linarith
  
  have h₇ : y = 10 := by
    have h₇₁ : 3 * y = 30 := h₆
    have h₇₂ : y = 10 := by
      linarith
    exact h₇₂
  
  rw [h₇]
  <;> norm_num
