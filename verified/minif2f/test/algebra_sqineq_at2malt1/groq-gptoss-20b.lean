import Mathlib

open scoped Nat
open scoped Real

theorem algebra_sqineq_at2malt1 (a : ℝ) : a * (2 - a) ≤ 1 := by
  have h : a * (2 - a) = 2 * a - a ^ 2 := by ring
  have hsub : 2 * a - a ^ 2 - 1 ≤ 0 := by
    have hneg : -(a - 1) ^ 2 ≤ 0 := by
      have hnonneg : 0 ≤ (a - 1) ^ 2 := by
        exact pow_two_nonneg (a - 1)
      exact neg_nonpos.mpr hnonneg
    have h_eq : 2 * a - a ^ 2 - 1 = -(a - 1) ^ 2 := by ring
    simpa [h_eq] using hneg
  have hle : 2 * a - a ^ 2 ≤ 1 := by
    have := add_le_add_right hsub 1
    simpa [sub_eq_add_neg, add_comm, add_left_comm, add_assoc] using this
  simpa [h] using hle
