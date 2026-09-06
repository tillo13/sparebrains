import Mathlib

open scoped Nat
open scoped Real

theorem algebra_sqineq_at2malt1 (a : ℝ) : a * (2 - a) ≤ 1 := by
  have h_eq : a * (2 - a) = 1 - (a - 1)^2 := by
    ring_nf
  calc
    a * (2 - a) = 1 - (a - 1)^2 := h_eq
    _ ≤ 1 := by
      have h : -(a - 1)^2 ≤ 0 := by
        have : 0 ≤ (a - 1)^2 := sq_nonneg _
        exact neg_nonpos.mpr this
      simpa [sub_eq_add_neg] using (add_le_add_left h 1)
