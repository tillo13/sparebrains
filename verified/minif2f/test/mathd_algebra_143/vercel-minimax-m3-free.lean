import Mathlib

open scoped Nat
open scoped Real

/-- If $f(x) = x + 1$ and $g(x) = x^2 + 3$, what is the value of $f(g(2))$? -/
theorem mathd_algebra_143 (f g : ℝ → ℝ) (h₀ : ∀ x, f x = x + 1) (h₁ : ∀ x, g x = x ^ 2 + 3) :
    f (g 2) = 8 := by
  have hg2 : g 2 = (2 : ℝ) ^ 2 + 3 := h₁ 2
  rw [hg2, h₀]
  norm_num
