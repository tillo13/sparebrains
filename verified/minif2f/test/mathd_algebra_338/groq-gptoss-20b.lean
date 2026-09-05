import Mathlib

open scoped Nat
open scoped Real

/-- If $3a + b + c = -3, a+3b+c = 9, a+b+3c = 19$, then find $abc$. -/
theorem mathd_algebra_338 (a b c : ℝ) (h₀ : 3 * a + b + c = -3) (h₁ : a + 3 * b + c = 9)
    (h₂ : a + b + 3 * c = 19) : a * b * c = -56 := by
  have h_a : a = -4 := by
    linarith
  have h_b : b = 2 := by
    linarith
  have h_c : c = 7 := by
    linarith
  calc
    a * b * c = (-4) * 2 * 7 := by
      simp [h_a, h_b, h_c]
    _ = -56 := by ring
