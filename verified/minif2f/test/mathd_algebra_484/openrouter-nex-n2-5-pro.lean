import Mathlib

open scoped Nat
open scoped Real

/-- Evaluate $\log_327$. -/
theorem mathd_algebra_484 : Real.log 27 / Real.log 3 = 3 := by
  have hlog : Real.log 27 = 3 * Real.log 3 := by
    rw [show (27 : ℝ) = (3 : ℝ) ^ 3 by norm_num]
    simpa using Real.log_pow (by norm_num : (0 : ℝ) < 3) 3
  have hden : Real.log 3 ≠ 0 :=
    Real.log_ne_zero_of_pos_of_ne_one (by norm_num : (0 : ℝ) < 3)
      (by norm_num : (3 : ℝ) ≠ 1)
  rw [hlog]
  field_simp [hden]
