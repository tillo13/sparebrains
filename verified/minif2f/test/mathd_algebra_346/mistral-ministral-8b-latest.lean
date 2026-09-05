import Mathlib

open scoped Nat
open scoped Real

/-- Let $f(x) = 2x-3$ and $g(x) = x+1$. What is the value of $g(f(5)-1)$? -/
theorem mathd_algebra_346 (f g : ℝ → ℝ) (h₀ : ∀ x, f x = 2 * x - 3) (h₁ : ∀ x, g x = x + 1) :
    g (f 5 - 1) = 7 := by
  have h_f_5 : f 5 = 2 * 5 - 3 := h₀ 5
  { rw [h_f_5, h₁]; ring }
