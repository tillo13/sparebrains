import Mathlib

/-- Natural Number Game (Lean 4), AdvMultiplication world, level 5: le_mul_right. Restated over Mathlib's ℕ. Source: https://github.com/leanprover-community/NNG4/blob/main/Game/Levels/AdvMultiplication/L05le_mul_right.lean, Apache-2.0. -/
theorem primer_advmultiplication_05_le_mul_right (a b : ℕ) (h : a * b ≠ 0) : a ≤ a * b := by
  -- Show that `b` is nonzero
  have hb0 : b ≠ 0 := by
    intro hb0
    have : a * b = 0 := by
      simpa [hb0] using mul_zero a
    exact h this
  -- From `b ≠ 0` we get `1 ≤ b`
  have hbpos : 0 < b := Nat.pos_of_ne_zero hb0
  -- Multiply the inequality `1 ≤ b` by `a` on the left
  have : a * 1 ≤ a * b := Nat.mul_le_mul_left a (Nat.succ_le_of_lt hbpos)
  -- Simplify `a * 1` to `a`
  simpa [Nat.mul_one] using this
