import Mathlib

/-- Natural Number Game (Lean 4), AdvMultiplication world, level 5: le_mul_right. Restated over Mathlib's ℕ. Source: https://github.com/leanprover-community/NNG4/blob/main/Game/Levels/AdvMultiplication/L05le_mul_right.lean, Apache-2.0. -/
theorem primer_advmultiplication_05_le_mul_right (a b : ℕ) (h : a * b ≠ 0) : a ≤ a * b := by
  -- From `a * b ≠ 0` we obtain `b ≠ 0`.
  have hne : a ≠ 0 ∧ b ≠ 0 := by
    have : ¬ (a = 0 ∨ b = 0) := by
      intro hzero
      have : a * b = 0 := (Nat.mul_eq_zero).2 hzero
      exact h this
    exact not_or.mp this
  have hbpos : 0 < b := Nat.pos_of_ne_zero hne.right
  have h1b : (1 : ℕ) ≤ b := Nat.succ_le_of_lt hbpos
  have : a * 1 ≤ a * b := Nat.mul_le_mul_left a h1b
  simpa using this
