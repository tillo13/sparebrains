import Mathlib

open scoped Nat
open scoped Real

/-- If $f(x) = \dfrac{1}{x + 2},$ what is $f(f(1))$? -/
theorem mathd_algebra_270 (f : ℝ → ℝ) (h₀ : ∀ x ≠ -2, f x = 1 / (x + 2)) :
    f (f 1) = 3 / 7 := by
  have h₁ : f 1 = 1 / 3 := by
    have h₁₀ : (1 : ℝ) ≠ -2 := by norm_num
    have h₁₁ : f 1 = 1 / (1 + 2 : ℝ) := by
      apply h₀
      exact h₁₀
    rw [h₁₁]
    <;> norm_num
    <;> field_simp
    <;> ring_nf
    <;> norm_num
  
  have h₂ : f (f 1) = 3 / 7 := by
    rw [h₁]
    have h₂₀ : (1 / 3 : ℝ) ≠ -2 := by norm_num
    have h₂₁ : f (1 / 3 : ℝ) = 1 / ((1 / 3 : ℝ) + 2) := by
      apply h₀
      exact h₂₀
    rw [h₂₁]
    <;> norm_num
    <;> field_simp
    <;> ring_nf
    <;> norm_num
  
  rw [h₂]
  <;> norm_num
