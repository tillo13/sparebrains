import Mathlib

open scoped Nat
open scoped Real

/-- If $f(x) = \dfrac{1}{x + 2},$ what is $f(f(1))$? -/
theorem mathd_algebra_270 (f : ℝ → ℝ) (h₀ : ∀ x ≠ -2, f x = 1 / (x + 2)) :
    f (f 1) = 3 / 7 := by
  have h1 : f 1 = 1 / 3 := by
    have hne : (1 : ℝ) ≠ -2 := by norm_num
    have h := h₀ 1 hne
    norm_num at h
    linarith
  rw [h1]
  have hne : (1 / 3 : ℝ) ≠ -2 := by norm_num
  have h := h₀ (1 / 3) hne
  norm_num at h
  linarith
