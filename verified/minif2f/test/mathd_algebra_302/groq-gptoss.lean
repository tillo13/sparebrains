import Mathlib

open scoped Nat
open scoped Real

/-- Evaluate $\left(\frac{i}{2}\right)^2$. -/
theorem mathd_algebra_302 : (Complex.I / 2) ^ 2 = -(1 / 4) := by
  calc
    (Complex.I / (2 : ℂ)) ^ 2
        = (Complex.I * Complex.I) / ((2 : ℂ) * (2 : ℂ)) := by
          field_simp [pow_two]
    _ = (Complex.I * Complex.I) / (4 : ℂ) := by
          norm_num
    _ = (-1) / (4 : ℂ) := by
          simpa [Complex.I_mul_I]
    _ = -(1 / 4) := by
          simpa [neg_div]
