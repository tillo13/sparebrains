import Mathlib

/-- Natural Number Game (Lean 4), Power world, level 6: pow_add. Restated over Mathlib's ℕ. Source: https://github.com/leanprover-community/NNG4/blob/main/Game/Levels/Power/L06pow_add.lean, Apache-2.0. -/
theorem primer_power_06_pow_add (a m n : ℕ) : a ^ (m + n) = a ^ m * a ^ n := by
  induction m with
  | zero => simp
  | succ k ih =>
    calc
      a ^ (k.succ + n) = a ^ (k + n).succ := by rw [Nat.succ_add]
      _ = a ^ (k + n) * a := by rw [pow_succ]
      _ = (a ^ k * a ^ n) * a := by rw [ih]
      _ = a ^ k * (a ^ n * a) := by simp [mul_assoc]
      _ = a ^ k * (a * a ^ n) := by rw [mul_comm (a ^ n) a]
      _ = (a ^ k * a) * a ^ n := by simp [mul_assoc]
      _ = a ^ k.succ * a ^ n := by rw [pow_succ]
