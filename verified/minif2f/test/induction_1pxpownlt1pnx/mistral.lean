import Mathlib

open scoped Nat
open scoped Real

theorem induction_1pxpownlt1pnx (x : ℝ) (n : ℕ) (h₀ : -1 < x) (h₁ : 0 < n) :
    1 + ↑n * x ≤ (1 + x) ^ (n : ℕ) := by
  induction n with
  | zero => linarith
  | succ n ih =>
    cases n
    · norm_num
      all_goals nlinarith
    · simp [pow_succ, pow_zero, mul_add, add_mul] at ih ⊢
      all_goals nlinarith [sq_nonneg x, sq_nonneg (x + 1), mul_nonneg (show 0 ≤ (x + 1) by linarith) (show 0 ≤ (x + 1) by linarith)]
