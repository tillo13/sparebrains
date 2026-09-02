import Mathlib

open scoped Nat
open scoped Real

/--
Real numbers $x$ and $y$ have an arithmetic mean of 7 and a geometric mean of $\sqrt{19}$. Find $x^2+y^2$. -/
theorem mathd_algebra_332 (x y : ℝ) (h₀ : (x + y) / 2 = 7) (h₁ : Real.sqrt (x * y) = Real.sqrt 19) :
    x ^ 2 + y ^ 2 = 158 := by
  have h2 : x + y = 14 := by linarith
  have h3 : x * y ≥ 0 := by
    have h4 : Real.sqrt (x * y) = Real.sqrt 19 := h₁
    have h5 : x * y ≥ 0 := by
      by_contra h
      push_neg at h
      have h6 : Real.sqrt (x * y) = 0 := by
        rw [Real.sqrt_eq_zero']
        nlinarith
        all_goals nlinarith
      rw [h6] at h4
      have h7 : Real.sqrt 19 > 0 := by
        apply Real.sqrt_pos.mpr
        all_goals norm_num
      linarith [h7, h4]
    linarith
  have h6 : x * y = 19 := by
    have h7 : Real.sqrt (x * y) = Real.sqrt 19 := h₁
    have h8 : x * y ≥ 0 := h3
    have h9 : (Real.sqrt (x * y)) ^ 2 = (Real.sqrt 19) ^ 2 := by
      rw [h7]
    rw [Real.sq_sqrt h8, Real.sq_sqrt (by norm_num)] at h9
    linarith
  have h7 : x ^ 2 + y ^ 2 = (x + y) ^ 2 - 2 * (x * y) := by ring
  rw [h7]
  rw [h2, h6]
  all_goals norm_num
