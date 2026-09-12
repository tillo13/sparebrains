import Mathlib

/-- Natural Number Game (Lean 4), AdvMultiplication world, level 5: le_mul_right. Restated over Mathlib's ℕ. Source: https://github.com/leanprover-community/NNG4/blob/main/Game/Levels/AdvMultiplication/L05le_mul_right.lean, Apache-2.0. -/
theorem primer_advmultiplication_05_le_mul_right (a b : ℕ) (h : a * b ≠ 0) : a ≤ a * b := by
  have hb0 : b ≠ 0 := by
    intro hb
    have : a * b = 0 := by
      simpa [hb] using Nat.mul_zero a
    exact h this
  have hbpos : 0 < b := Nat.pos_of_ne_zero hb0
  have hb1 : 1 ≤ b := Nat.succ_le_of_lt hbpos
  have : a * 1 ≤ a * b := Nat.mul_le_mul_left a hb1
  simpa [Nat.mul_one] using this
