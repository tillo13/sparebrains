import Mathlib

open scoped Nat
open scoped Real

/-- What value of $x$ will give the minimum value for $x^2- 14x + 3$? -/
theorem mathd_algebra_113 (x : ℝ) : x ^ 2 - 14 * x + 3 ≥ 7 ^ 2 - 14 * 7 + 3 := by
  have h0 : 0 ≤ (x - 7) ^ 2 := by
    exact sq_nonneg (x - 7)
  have h1 : -46 ≤ (x - 7) ^ 2 - 46 := by
    simpa [sub_eq_add_neg, add_comm, add_left_comm, add_assoc] using
      add_le_add_right h0 (-46)
  calc
    x ^ 2 - 14 * x + 3
        = (x - 7) ^ 2 - 46 := by ring
    _ ≥ -46 := by
      exact h1
    _ = 7 ^ 2 - 14 * 7 + 3 := by ring
