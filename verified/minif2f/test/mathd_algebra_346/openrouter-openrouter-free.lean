import Mathlib

open scoped Nat
open scoped Real

/-- Let $f(x) = 2x-3$ and $g(x) = x+1$. What is the value of $g(f(5)-1)$? -/
theorem mathd_algebra_346 (f g : ℝ → ℝ) (h₀ : ∀ x, f x = 2 * x - 3) (h₁ : ∀ x, g x = x + 1) :
    g (f 5 - 1) = 7 := by
  have h2 : f 5 = 2 * 5 - 3 := by
    rw [h₀]
  have h3 : f 5 - 1 = 2 * 5 - 3 - 1 := by
    rw [h2]
  have h4 : f 5 - 1 = 6 := by
    norm_num at h3
    exact h3
  have h5 : g (f 5 - 1) = g 6 := by
    rw [h4]
  have h6 : g 6 = 6 + 1 := by
    rw [h₁]
  have h7 : g (f 5 - 1) = 7 := by
    rw [h5, h6]
    norm_num
  exact h7
