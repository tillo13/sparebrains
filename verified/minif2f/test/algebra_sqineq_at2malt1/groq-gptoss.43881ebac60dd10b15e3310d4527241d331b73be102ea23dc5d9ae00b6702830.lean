import Mathlib

open scoped Nat
open scoped Real

theorem algebra_sqineq_at2malt1 (a : ℝ) : a * (2 - a) ≤ 1 := by
  have h_eq : a * (2 - a) = 1 - (a - 1) ^ 2 := by
    ring
  have h0 : (0 : ℝ) ≤ (a - 1) ^ 2 := by
    exact sq_nonneg (a - 1)
  have hneg : -(a - 1) ^ 2 ≤ (0 : ℝ) := by
    simpa [neg_nonpos] using h0
  have : 1 - (a - 1) ^ 2 ≤ (1 : ℝ) := by
    simpa [sub_eq_add_neg] using add_le_add_left hneg 1
  simpa [h_eq] using this
