import Mathlib

open scoped Nat
open scoped Real

/--
Real numbers $x$ and $y$ have an arithmetic mean of 7 and a geometric mean of $\sqrt{19}$. Find $x^2+y^2$. -/
theorem mathd_algebra_332 (x y : ℝ) (h₀ : (x + y) / 2 = 7) (h₁ : Real.sqrt (x * y) = Real.sqrt 19) :
    x ^ 2 + y ^ 2 = 158 := by
  have h_sum : x + y = 14 := by linarith [h₀]
  have hxy_nonneg : 0 ≤ x * y := by
    by_contra h
    have hxy_neg : x * y < 0 := by linarith
    have hsqrt_xy : Real.sqrt (x * y) = 0 := by
      apply Real.sqrt_eq_zero_of_nonpos
      linarith
    have hsqrt_19_pos : Real.sqrt 19 > 0 := Real.sqrt_pos.mpr (by norm_num)
    linarith [h₁, hsqrt_xy, hsqrt_19_pos]
  have h_prod : x * y = 19 := by
    have h_sq : (Real.sqrt (x * y)) ^ 2 = (Real.sqrt 19) ^ 2 := by rw [h₁]
    rw [Real.sq_sqrt hxy_nonneg, Real.sq_sqrt (by norm_num : 0 ≤ (19 : ℝ))] at h_sq
    exact h_sq
  calc
    x ^ 2 + y ^ 2 = (x + y) ^ 2 - 2 * (x * y) := by ring
    _ = 14 ^ 2 - 2 * 19 := by rw [h_sum, h_prod]
    _ = 158 := by norm_num
