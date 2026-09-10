import Mathlib

open scoped Nat
open scoped Real

/-- What value of $x$ will give the minimum value for $x^2- 14x + 3$? -/
theorem mathd_algebra_113 (x : ℝ) : x ^ 2 - 14 * x + 3 ≥ 7 ^ 2 - 14 * 7 + 3 := by
  have h : 0 ≤ (x - 7) ^ 2 := by
    exact sq_nonneg _
  calc
    x ^ 2 - 14 * x + 3
        = (x - 7) ^ 2 - 46 := by ring
    _ ≥ 0 - 46 := by
      have : (x - 7) ^ 2 ≥ 0 := by
        simpa [ge_iff_le] using h
      linarith
    _ = 7 ^ 2 - 14 * 7 + 3 := by ring
