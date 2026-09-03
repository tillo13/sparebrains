import Mathlib

open scoped Nat
open scoped Real

/-- If $f(x) = x + 1$ and $g(x) = x^2 + 3$, what is the value of $f(g(2))$? -/
theorem mathd_algebra_143 (f g : ℝ → ℝ) (h₀ : ∀ x, f x = x + 1) (h₁ : ∀ x, g x = x ^ 2 + 3) :
    f (g 2) = 8 := by
  calc
    f (g 2) = (g 2) + 1 := by
      simpa using h₀ (g 2)
    _ = (2 ^ 2 + 3) + 1 := by
      simpa [h₁]
    _ = 8 := by norm_num
