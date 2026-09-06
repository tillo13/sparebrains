import Mathlib

open scoped Nat
open scoped Real

/--
The graphs of $y=x^4$ and $y=5x^2-6$ intersect at four points with $x$-coordinates $\pm \sqrt{m}$ and $\pm \sqrt{n}$, where $m > n$. What is $m-n$? -/
theorem mathd_algebra_156 (x y : ℝ) (f g : ℝ → ℝ) (h₀ : ∀ t, f t = t ^ 4)
    (h₁ : ∀ t, g t = 5 * t ^ 2 - 6) (h₂ : f x = g x) (h₃ : f y = g y) (h₄ : x ^ 2 < y ^ 2) :
    y ^ 2 - x ^ 2 = 1 := by
  have hx : x ^ 4 = 5 * x ^ 2 - 6 := by
    simp only [h₀, h₁] at h₂
    exact h₂
  have hy : y ^ 4 = 5 * y ^ 2 - 6 := by
    simp only [h₀, h₁] at h₃
    exact h₃
  have hx_eq : (x ^ 2 - 2) * (x ^ 2 - 3) = 0 := by
    have : x ^ 4 - 5 * x ^ 2 + 6 = 0 := by linarith
    have factor : x ^ 4 - 5 * x ^ 2 + 6 = (x ^ 2 - 2) * (x ^ 2 - 3) := by ring
    linarith
  have hy_eq : (y ^ 2 - 2) * (y ^ 2 - 3) = 0 := by
    have : y ^ 4 - 5 * y ^ 2 + 6 = 0 := by linarith
    have factor : y ^ 4 - 5 * y ^ 2 + 6 = (y ^ 2 - 2) * (y ^ 2 - 3) := by ring
    linarith
  have hx23 : x ^ 2 = 2 ∨ x ^ 2 = 3 := by
    rcases mul_eq_zero.mp hx_eq with hx2 | hx3
    · exact Or.inl (by linarith)
    · exact Or.inr (by linarith)
  have hy23 : y ^ 2 = 2 ∨ y ^ 2 = 3 := by
    rcases mul_eq_zero.mp hy_eq with hy2 | hy3
    · exact Or.inl (by linarith)
    · exact Or.inr (by linarith)
  have h_x2y3 : x ^ 2 = 2 ∧ y ^ 2 = 3 := by
    cases hx23 with
    | inl hx2 =>
      cases hy23 with
      | inl hy2 => linarith
      | inr hy3 => exact ⟨hx2, hy3⟩
    | inr hx3 =>
      cases hy23 with
      | inl hy2 => linarith
      | inr hy3 => linarith
  linarith
