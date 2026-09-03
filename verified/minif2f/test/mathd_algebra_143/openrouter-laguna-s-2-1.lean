import Mathlib

open scoped Nat
open scoped Real

/-- If $f(x) = x + 1$ and $g(x) = x^2 + 3$, what is the value of $f(g(2))$? -/
theorem mathd_algebra_143 (f g : ℝ → ℝ) (h₀ : ∀ x, f x = x + 1) (h₁ : ∀ x, g x = x ^ 2 + 3) :
    f (g 2) = 8 := by
  have h₂ : g 2 = 2 ^ 2 + 3 := by rw [h₁]
  have h₃ : g 2 = 7 := by norm_num at h₂; exact h₂
  have h₄ : f (g 2) = f 7 := by rw [h₃]
  have h₅ : f 7 = 7 + 1 := by rw [h₀]
  have h₆ : f (g 2) = 8 := by rw [h₄, h₅]; norm_num
  exact h₆
