import Mathlib

/-- Natural Number Game (Lean 4), AdvMultiplication world, level 4: one_le_of_ne_zero. Restated over Mathlib's ℕ. Source: https://github.com/leanprover-community/NNG4/blob/main/Game/Levels/AdvMultiplication/L04one_le_of_ne_zero.lean, Apache-2.0. -/
theorem primer_advmultiplication_04_one_le_of_ne_zero (a : ℕ) (ha : a ≠ 0) : 1 ≤ a := by
  have h_main : 1 ≤ a := by
    have h : 1 ≤ a ↔ a ≠ 0 := by
      apply Nat.one_le_iff_ne_zero
    rw [h]
    exact ha
  exact h_main
