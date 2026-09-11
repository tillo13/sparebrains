import Mathlib

/-- Mathematics in Lean, Chapter 3 §1 (Implication and the Universal Quantifier), exercise 1. Avigad & Massot, Apache-2.0, commit dd6d752. -/
theorem mil_c03_s01_ex01 :
    ∀ {x y ε : ℝ}, 0 < ε → ε ≤ 1 → |x| < ε → |y| < ε → |x * y| < ε := by
  intro x y ε hε hε_le hx hy
  calc
    |x * y| = |x| * |y| := by exact abs_mul x y
    _ < ε * ε := by
      exact mul_lt_mul'' hx hy (abs_nonneg x) (abs_nonneg y)
    _ ≤ ε := by
      exact mul_le_of_le_one_right (le_of_lt hε) hε_le
