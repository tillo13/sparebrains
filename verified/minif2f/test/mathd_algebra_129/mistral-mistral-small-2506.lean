import Mathlib

open scoped Nat
open scoped Real

/-- Solve for $a$: $\dfrac{8^{-1}}{4^{-1}}-a^{-1}=1$. -/
theorem mathd_algebra_129 (a : ℝ) (h₀ : a ≠ 0) (h₁ : 8⁻¹ / 4⁻¹ - a⁻¹ = 1) : a = -2 := by
  field_simp [h₀, show (8 : ℝ) ≠ 0 by norm_num, show (4 : ℝ) ≠ 0 by norm_num] at h₁
  ring_nf at h₁
  have h₂ : a = -2 := by
    nlinarith [sq_pos_of_ne_zero h₀]
  exact h₂
