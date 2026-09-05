import Mathlib

open scoped Nat
open scoped Real

/-- Solve  \[\frac{x-9}{x+1}=2\]for $x$. -/
theorem mathd_algebra_80 (x : ℝ) (h₀ : x ≠ -1) (h₁ : (x - 9) / (x + 1) = 2) : x = -11 := by
  have h0 : x + 1 ≠ 0 := by
    intro h
    apply h₀
    linarith
  have h2 : 2 * (x + 1) = x - 9 := (div_eq_iff_mul_eq h0).mp h₁
  have : x = -11 := by
    linarith [h2]
  exact this
