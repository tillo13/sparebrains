import Mathlib

open scoped Nat
open scoped Real

/-- If $f(x) = \dfrac{1}{x + 2},$ what is $f(f(1))$? -/
theorem mathd_algebra_270 (f : ℝ → ℝ) (h₀ : ∀ x ≠ -2, f x = 1 / (x + 2)) :
    f (f 1) = 3 / 7 := by
  have h1 : f 1 = 1 / 3 := by
    have h : (1 : ℝ) ≠ -2 := by norm_num
    have eq : f 1 = 1 / (1 + 2) := h₀ 1 h
    rw [eq]
    norm_num
  have h2 : f (1 / 3) = 3 / 7 := by
    have h : (1 / 3 : ℝ) ≠ -2 := by norm_num
    have eq : f (1 / 3) = 1 / (1 / 3 + 2) := h₀ (1 / 3) h
    rw [eq]
    norm_num
  rw [h1, h2]
