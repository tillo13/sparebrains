import Mathlib

/-- Mathematics in Lean, Chapter 3 §1 (Implication and the Universal Quantifier), exercise 1. Avigad & Massot, Apache-2.0, commit dd6d752. -/
theorem mil_c03_s01_ex01 :
    ∀ {x y ε : ℝ}, 0 < ε → ε ≤ 1 → |x| < ε → |y| < ε → |x * y| < ε := by
  intros x y ε hε hε1 hx hy
  rw [abs_mul]
  have hy_le_one : |y| ≤ 1 := le_of_lt (lt_of_lt_of_le hy hε1)
  have h : |x| * |y| ≤ |x| := by
    calc
      |x| * |y| = |y| * |x| := by rw [mul_comm]
      _ ≤ 1 * |x| := mul_le_mul_of_nonneg_right hy_le_one (abs_nonneg x)
      _ = |x| := by rw [one_mul]
  exact lt_of_le_of_lt h hx
