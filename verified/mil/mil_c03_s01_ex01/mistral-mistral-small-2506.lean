import Mathlib

/-- Mathematics in Lean, Chapter 3 §1 (Implication and the Universal Quantifier), exercise 1. Avigad & Massot, Apache-2.0, commit dd6d752. -/
theorem mil_c03_s01_ex01 :
    ∀ {x y ε : ℝ}, 0 < ε → ε ≤ 1 → |x| < ε → |y| < ε → |x * y| < ε := by
  intro x y ε hε hε1 hx hy
  have h1 : |x * y| = |x| * |y| := by
    rw [abs_mul]
  rw [h1]
  have h2 : |x| * |y| < ε * ε := by
    nlinarith [abs_nonneg x, abs_nonneg y, hx, hy]
  have h3 : ε * ε ≤ ε := by
    nlinarith [hε, hε1]
  nlinarith [abs_nonneg (x * y)]
