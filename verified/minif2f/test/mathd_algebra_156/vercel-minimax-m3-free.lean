import Mathlib

open scoped Nat
open scoped Real

/--
The graphs of $y=x^4$ and $y=5x^2-6$ intersect at four points with $x$-coordinates $\pm \sqrt{m}$ and $\pm \sqrt{n}$, where $m > n$. What is $m-n$? -/
theorem mathd_algebra_156 (x y : ℝ) (f g : ℝ → ℝ) (h₀ : ∀ t, f t = t ^ 4)
    (h₁ : ∀ t, g t = 5 * t ^ 2 - 6) (h₂ : f x = g x) (h₃ : f y = g y) (h₄ : x ^ 2 < y ^ 2) :
    y ^ 2 - x ^ 2 = 1 := by
  have hx : x ^ 4 = 5 * x ^ 2 - 6 := by linarith [h₀ x, h₁ x, h₂]
  have hy : y ^ 4 = 5 * y ^ 2 - 6 := by linarith [h₀ y, h₁ y, h₃]
  have hx' : x ^ 4 - 5 * x ^ 2 + 6 = 0 := by linarith
  have hy' : y ^ 4 - 5 * y ^ 2 + 6 = 0 := by linarith
  have hx'' : (x ^ 2 - 2) * (x ^ 2 - 3) = 0 := by
    ring_nf; linarith
  have hy'' : (y ^ 2 - 2) * (y ^ 2 - 3) = 0 := by
    ring_nf; linarith
  rcases mul_eq_zero.mp hx'' with h | h <;> rcases mul_eq_zero.mp hy'' with hm | hm <;>
    simp only [sub_eq_zero] at *
  · linarith [h, hm]
  · linarith [h, hm]
  · linarith [h, hm]
  · linarith [h, hm]
