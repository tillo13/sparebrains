import Mathlib

open scoped Nat
open scoped Real

/-- Let $f(x) = 2x-3$ and $g(x) = x+1$. What is the value of $g(f(5)-1)$? -/
theorem mathd_algebra_346 (f g : ℝ → ℝ) (h₀ : ∀ x, f x = 2 * x - 3) (h₁ : ∀ x, g x = x + 1) :
    g (f 5 - 1) = 7 := by
  have h₂ : f 5 = 7 := by
    have h₂₁ : f 5 = 2 * (5 : ℝ) - 3 := by
      rw [h₀]
      <;> norm_num
    rw [h₂₁]
    <;> norm_num
  
  have h₃ : f 5 - 1 = 6 := by
    rw [h₂]
    <;> norm_num
  
  have h₄ : g (f 5 - 1) = 7 := by
    have h₄₁ : g (f 5 - 1) = (f 5 - 1 : ℝ) + 1 := by
      have h₄₂ := h₁ (f 5 - 1)
      ring_nf at h₄₂ ⊢
      <;> linarith
    rw [h₄₁]
    rw [h₃]
    <;> norm_num
  
  rw [h₄]
  <;> norm_num
