import Mathlib

/-- Mathematics in Lean, Chapter 2 §1 (Calculating), exercise 2. Avigad & Massot, Apache-2.0, commit dd6d752. -/
theorem mil_c02_s01_ex02 (a b c : ℝ) : a * (b * c) = b * (a * c) := by
  calc
    a * (b * c) = (a * b) * c := by
      simpa using (mul_assoc a b c).symm
    _ = (b * a) * c := by
      simpa [mul_comm]
    _ = b * (a * c) := by
      simpa using (mul_assoc b a c)
