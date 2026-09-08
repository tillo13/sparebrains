import Mathlib

open scoped Nat
open scoped Real

/-- What value of $x$ will give the minimum value for $x^2- 14x + 3$? -/
theorem mathd_algebra_113 (x : ℝ) : x ^ 2 - 14 * x + 3 ≥ 7 ^ 2 - 14 * 7 + 3 := by
  have h_main : x ^ 2 - 14 * x + 3 = (x - 7) ^ 2 + (7 ^ 2 - 14 * 7 + 3) := by
    have h1 : (x - 7) ^ 2 = x ^ 2 - 14 * x + 49 := by
      ring
    have h2 : 7 ^ 2 - 14 * 7 + 3 = -46 := by norm_num
    have h3 : x ^ 2 - 14 * x + 3 = (x - 7) ^ 2 + (7 ^ 2 - 14 * 7 + 3) := by
      rw [h1]
      norm_num at h2 ⊢
      <;> linarith
    exact h3
  
  have h_final : x ^ 2 - 14 * x + 3 ≥ 7 ^ 2 - 14 * 7 + 3 := by
    have h1 : (x - 7) ^ 2 ≥ 0 := by nlinarith
    have h2 : x ^ 2 - 14 * x + 3 = (x - 7) ^ 2 + (7 ^ 2 - 14 * 7 + 3) := h_main
    have h3 : x ^ 2 - 14 * x + 3 ≥ 7 ^ 2 - 14 * 7 + 3 := by
      linarith
    exact h3
  
  exact h_final
