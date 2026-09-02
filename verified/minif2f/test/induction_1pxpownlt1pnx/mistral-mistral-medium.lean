import Mathlib

open scoped Nat
open scoped Real

theorem induction_1pxpownlt1pnx (x : ℝ) (n : ℕ) (h₀ : -1 < x) (h₁ : 0 < n) :
    1 + ↑n * x ≤ (1 + x) ^ (n : ℕ) := by
  induction n with
  | zero => linarith
  | succ n ih =>
    cases n with
    | zero =>
      simp
      all_goals linarith
    | succ n =>
      simp [pow_succ, mul_add, add_mul] at ih ⊢
      nlinarith [sq_nonneg (x + 1), sq_nonneg (x), ih, h₀]
