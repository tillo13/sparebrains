import Mathlib

open scoped Nat
open scoped Real

/-- Evaluate $\left(\frac{i}{2}\right)^2$. -/
theorem mathd_algebra_302 : (Complex.I / 2) ^ 2 = -(1 / 4) := by
  calc
    (Complex.I / 2) ^ 2
        = Complex.I ^ 2 / (2 : ℂ) ^ 2 := by
          simpa [div_pow]
    _ = (-1) / (2 : ℂ) ^ 2 := by
          simpa [pow_two, Complex.I_mul_I]
    _ = -(1 / (2 : ℂ) ^ 2) := by
          simpa [neg_div]
    _ = -(1 / 4) := by
          norm_num
