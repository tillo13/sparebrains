import Mathlib

open scoped Nat
open scoped Real

theorem algebra_sqineq_at2malt1 (a : ℝ) : a * (2 - a) ≤ 1 := by
  calc
    a * (2 - a) = 1 - (a - 1) ^ 2 := by ring
    _ ≤ 1 := by
      have hneg : -(a - 1) ^ 2 ≤ (0 : ℝ) := by
        exact neg_nonpos.mpr (sq_nonneg _)
      have h := add_le_add_left hneg 1
      simpa [sub_eq_add_neg] using h
