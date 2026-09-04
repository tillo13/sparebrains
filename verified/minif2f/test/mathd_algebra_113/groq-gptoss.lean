import Mathlib

open scoped Nat
open scoped Real

/-- What value of $x$ will give the minimum value for $x^2- 14x + 3$? -/
theorem mathd_algebra_113 (x : ℝ) : x ^ 2 - 14 * x + 3 ≥ 7 ^ 2 - 14 * 7 + 3 := by
  have hdiff :
      (x ^ 2 - 14 * x + 3) - (7 ^ 2 - 14 * 7 + 3) = (x - 7) ^ 2 := by
    ring
  have hnonneg : (0 : ℝ) ≤ (x - 7) ^ 2 := by
    exact pow_two_nonneg _
  have : (0 : ℝ) ≤ (x ^ 2 - 14 * x + 3) - (7 ^ 2 - 14 * 7 + 3) := by
    simpa [hdiff] using hnonneg
  exact (sub_nonneg.mp this)
