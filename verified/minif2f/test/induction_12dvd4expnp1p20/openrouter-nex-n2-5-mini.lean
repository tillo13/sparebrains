import Mathlib

open scoped Nat
open scoped Real

theorem induction_12dvd4expnp1p20 (n : ℕ) : 12 ∣ 4 ^ (n + 1) + 20 := by
  induction n with
  | zero => norm_num
  | succ n ih =>
      have h : 12 ∣ 3 * 4 ^ (n + 1) := by
        rw [show 3 * 4 ^ (n + 1) = 12 * 4 ^ n by ring]
        exact Nat.dvd_mul_right 12 (4 ^ n)
      calc
        12 ∣ (4 ^ (n + 1) + 20) + 3 * 4 ^ (n + 1) := Nat.dvd_add ih h
        _ = 4 ^ (n + 2) + 20 := by ring
