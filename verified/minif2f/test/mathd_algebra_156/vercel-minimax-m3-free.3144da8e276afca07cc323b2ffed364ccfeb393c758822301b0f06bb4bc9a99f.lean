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
  have hx2 : x ^ 2 = 2 ∨ x ^ 2 = 3 := by
    have h6 : (x ^ 2 - 2) * (x ^ 2 - 3) = 0 := by
      have h : x ^ 4 - 5 * x ^ 2 + 6 = 0 := by linarith
      ring_nf at h; ring_nf; linarith
    exact Or.imp (fun h => by linarith) (fun h => by linarith) (mul_eq_zero.mp h6)
  have hy2 : y ^ 2 = 2 ∨ y ^ 2 = 3 := by
    have h6 : (y ^ 2 - 2) * (y ^ 2 - 3) = 0 := by
      have h : y ^ 4 - 5 * y ^ 2 + 6 = 0 := by linarith
      ring_nf at h; ring_nf; linarith
    exact Or.imp (fun h => by linarith) (fun h => by linarith) (mul_eq_zero.mp h6)
  rcases hx2 with hx2 | hx2 <;> rcases hy2 with hy2 | hy2 <;> linarith
