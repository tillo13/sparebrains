import Mathlib

open scoped Nat
open scoped Real

/--
Real numbers $x$ and $y$ have an arithmetic mean of 7 and a geometric mean of $\sqrt{19}$. Find $x^2+y^2$. -/
theorem mathd_algebra_332 (x y : ℝ) (h₀ : (x + y) / 2 = 7) (h₁ : Real.sqrt (x * y) = Real.sqrt 19) :
    x ^ 2 + y ^ 2 = 158 := by
  have h2 : x + y = 14 := by linarith
  have h3 : x * y ≥ 0 := by
    have h4 : Real.sqrt (x * y) ≥ 0 := Real.sqrt_nonneg (x * y)
    have h5 : Real.sqrt 19 ≥ 0 := Real.sqrt_nonneg 19
    have h6 : x * y ≥ 0 := by
      by_contra h
      push_neg at h
      have h7 : Real.sqrt (x * y) = 0 := Real.sqrt_eq_zero'.mpr (le_of_lt h)
      rw [h7] at h₁
      have h8 : Real.sqrt 19 = 0 := by linarith
      have h9 : (19 : ℝ) = 0 := by
        have h10 : Real.sqrt 19 ≥ 0 := Real.sqrt_nonneg 19
        have h11 : (Real.sqrt 19) ^ 2 = 19 := Real.sq_sqrt (by norm_num)
        rw [h8] at h11
        linarith
      norm_num at h9
    linarith
  have h4 : x * y = 19 := by
    have h5 : (Real.sqrt (x * y)) ^ 2 = x * y := Real.sq_sqrt h3
    have h6 : (Real.sqrt 19) ^ 2 = 19 := Real.sq_sqrt (by norm_num)
    rw [h₁] at h5
    linarith
  have h7 : x ^ 2 + y ^ 2 = (x + y) ^ 2 - 2 * (x * y) := by ring
  rw [h7, h2, h4]
  norm_num
