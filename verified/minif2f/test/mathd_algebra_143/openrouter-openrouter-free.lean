import Mathlib

open scoped Nat
open scoped Real

/-- If $f(x) = x + 1$ and $g(x) = x^2 + 3$, what is the value of $f(g(2))$? -/
theorem mathd_algebra_143 (f g : ℝ → ℝ) (h₀ : ∀ x, f x = x + 1) (h₁ : ∀ x, g x = x ^ 2 + 3) :
    f (g 2) = 8 := by
  have h₂ : g 2 = 7 := by
    have h₂₁ : g 2 = (2 : ℝ) ^ 2 + 3 := by
      have h₂₂ := h₁ 2
      norm_num at h₂₂ ⊢
      <;> linarith
    rw [h₂₁]
    <;> norm_num
  
  have h₃ : f (g 2) = 8 := by
    have h₃₁ : f (g 2) = f 7 := by
      rw [h₂]
      <;> norm_num
    rw [h₃₁]
    have h₃₂ : f 7 = (7 : ℝ) + 1 := by
      have h₃₃ := h₀ 7
      norm_num at h₃₃ ⊢
      <;> linarith
    rw [h₃₂]
    <;> norm_num
  
  rw [h₃]
  <;> norm_num
