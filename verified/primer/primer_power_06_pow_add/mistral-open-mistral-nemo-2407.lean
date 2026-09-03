import Mathlib

/-- Natural Number Game (Lean 4), Power world, level 6: pow_add. Restated over Mathlib's ℕ. Source: https://github.com/leanprover-community/NNG4/blob/main/Game/Levels/Power/L06pow_add.lean, Apache-2.0. -/
theorem primer_power_06_pow_add (a m n : ℕ) : a ^ (m + n) = a ^ m * a ^ n := by
  induction' m with m ih;
  { simp [pow_zero, pow_succ, mul_one] }
  simp [pow_succ, ih, mul_comm, pow_add]
