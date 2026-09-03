import Mathlib

/-- Mathematics in Lean, Chapter 2 §1 (Calculating), exercise 1. Avigad & Massot, Apache-2.0, commit dd6d752. -/
theorem mil_c02_s01_ex01 (a b c : ℝ) : c * b * a = b * (a * c) := by
  calc
    c * b * a = (c * b) * a := by rfl
    _ = c * (b * a) := by rw [mul_assoc]
    _ = c * (a * b) := by rw [mul_comm b a]
    _ = (c * a) * b := by rw [mul_assoc]
    _ = (a * c) * b := by rw [mul_comm c a]
    _ = a * (c * b) := by rw [mul_assoc]
    _ = a * (b * c) := by rw [mul_comm c b]
    _ = b * (a * c) := by rw [mul_left_comm a b c]
