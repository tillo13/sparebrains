import Mathlib

/-- Mathematics in Lean, Chapter 2 §1 (Calculating), exercise 5. Avigad & Massot, Apache-2.0, commit dd6d752. -/
theorem mil_c02_s01_ex05 (a b c d e f : ℝ) (h : b * c = e * f) : a * b * c * d = a * e * f * d := by
  calc
    a * b * c * d = a * (b * c) * d := by
      -- use mul_assoc
      simp [mul_comm, mul_left_comm, mul_assoc]
    _ = a * (e * f) * d := by
      simpa [h]
    _ = a * e * f * d := by
      -- use mul_assoc
      simp [mul_comm, mul_left_comm, mul_assoc]
