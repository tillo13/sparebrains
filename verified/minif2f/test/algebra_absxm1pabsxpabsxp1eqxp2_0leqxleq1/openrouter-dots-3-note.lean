import Mathlib

open scoped Nat
open scoped Real

theorem algebra_absxm1pabsxpabsxp1eqxp2_0leqxleq1 (x : ℝ)
    (h₀ : abs (x - 1) + abs x + abs (x + 1) = x + 2) : 0 ≤ x ∧ x ≤ 1 := by
  by_cases hx_nonneg : 0 ≤ x
  · by_cases hx_le_one : x ≤ 1
    · exact ⟨hx_nonneg, hx_le_one⟩
    · have hx_gt_one : 1 < x := by linarith
      have h1 : 0 ≤ x - 1 := by linarith
      have h2 : 0 ≤ x + 1 := by linarith
      rw [abs_of_nonneg h1, abs_of_nonneg hx_nonneg, abs_of_nonneg h2] at h₀
      have : x = 1 := by linarith
      linarith -- this gives contradiction with hx_gt_one, so we can close goal
  · have hx_neg : x < 0 := by linarith
    by_cases hx_ge_minus_one : -1 ≤ x
    · have h1 : x - 1 < 0 := by linarith
      have h2 : 0 ≤ x + 1 := by linarith
      rw [abs_of_neg h1, abs_of_neg hx_neg, abs_of_nonneg h2] at h₀
      have : x = 0 := by linarith
      linarith -- contradiction with hx_neg
    · have h_lt_minus_one : x < -1 := by linarith
      have h1 : x - 1 < 0 := by linarith
      have h2 : x + 1 < 0 := by linarith
      rw [abs_of_neg h1, abs_of_neg hx_neg, abs_of_neg h2] at h₀
      have : x = -1/2 := by linarith
      linarith -- contradiction
