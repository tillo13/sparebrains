import Mathlib

open scoped Nat
open scoped Real

theorem algebra_sqineq_at2malt1 (a : ℝ) : a * (2 - a) ≤ 1 := by
  have h_eq : a * (2 - a) = 1 - (a - 1) ^ 2 := by
    ring
  have hle : -(a - 1) ^ 2 ≤ (0 : ℝ) := (neg_nonpos).mpr (sq_nonneg _)
  have : 1 - (a - 1) ^ 2 ≤ 1 := by
    simpa [sub_eq_add_neg] using add_le_add_left hle 1
  simpa [h_eq] using this
