import Mathlib

/-- Natural Number Game (Lean 4), Power world, level 7: mul_pow. Restated over Mathlib's ℕ. Source: https://github.com/leanprover-community/NNG4/blob/main/Game/Levels/Power/L07mul_pow.lean, Apache-2.0. -/
theorem primer_power_07_mul_pow (a b n : ℕ) : (a * b) ^ n = a ^ n * b ^ n := by
  induction n with
  | zero => simp
  | succ n ih =>
    calc
      (a * b) ^ (n + 1) = (a * b) ^ n * (a * b) := pow_succ _ _
      _ = (a ^ n * b ^ n) * (a * b) := by rw [ih]
      _ = a ^ n * b ^ n * a * b := by ring
      _ = a ^ n * a * b ^ n * b := by ring
      _ = (a ^ n * a) * (b ^ n * b) := by ring
      _ = a ^ (n + 1) * b ^ (n + 1) := by rw [pow_succ, pow_succ]
