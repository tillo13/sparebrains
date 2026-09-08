import Mathlib

open scoped Nat
open scoped Real

/-- Solve  \[\frac{x-9}{x+1}=2\]for $x$. -/
theorem mathd_algebra_80 (x : ℝ) (h₀ : x ≠ -1) (h₁ : (x - 9) / (x + 1) = 2) : x = -11 := by
  have h₂ : x - 9 = 2 * (x + 1) := by
    have h₃ : x + 1 ≠ 0 := by
      intro h
      have : x = -1 := by linarith
      exact h₀ this
    rw [div_eq_iff h₃] at h₁
    exact h₁
  linarith
