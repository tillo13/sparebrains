import Mathlib

open scoped Nat
open scoped Real

/--
What digit must be placed in the blank to make the four-digit integer $20\_7$ a multiple of 11? -/
theorem mathd_numbertheory_293 (n : ℕ) (h₀ : n ≤ 9) (h₁ : 11 ∣ 20 * 100 + 10 * n + 7) : n = 5 := by
  interval_cases n
  · -- n = 0
    norm_num at h₁
  · -- n = 1
    norm_num at h₁
  · -- n = 2
    norm_num at h₁
  · -- n = 3
    norm_num at h₁
  · -- n = 4
    norm_num at h₁
  · -- n = 5
    rfl
  · -- n = 6
    norm_num at h₁
  · -- n = 7
    norm_num at h₁
  · -- n = 8
    norm_num at h₁
  · -- n = 9
    norm_num at h₁
