import Mathlib

open scoped Nat
open scoped Real

/-- Evaluate $\log_327$. -/
theorem mathd_algebra_484 : Real.log 27 / Real.log 3 = 3 := by
  have hpos : (0 : ℝ) < (3 : ℝ) := by norm_num
  have hlog : Real.log ((3 : ℝ) ^ 3) = (3 : ℝ) * Real.log 3 := by
    simpa using Real.log_pow hpos (n := 3)
  have h27 : (27 : ℝ) = (3 : ℝ) ^ 3 := by norm_num
  have hlog3_ne : Real.log 3 ≠ 0 := by
    have hpos_log : (0 : ℝ) < Real.log 3 := by
      have : (1 : ℝ) < 3 := by norm_num
      exact Real.log_pos this
    exact ne_of_gt hpos_log
  calc
    Real.log 27 / Real.log 3 = Real.log ((3 : ℝ) ^ 3) / Real.log 3 := by
      simpa [h27]
    _ = ((3 : ℝ) * Real.log 3) / Real.log 3 := by
      rw [hlog]
    _ = 3 := by
      field_simp [hlog3_ne]
