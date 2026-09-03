import Mathlib

/-- Natural Number Game (Lean 4), AdvAddition world, level 6: add_left_eq_zero. Restated over Mathlib's ℕ. Source: https://github.com/leanprover-community/NNG4/blob/main/Game/Levels/AdvAddition/L06add_left_eq_zero.lean, Apache-2.0. -/
theorem primer_advaddition_06_add_left_eq_zero (a b : ℕ) : a + b = 0 → b = 0 := by
  intro h
  have h1 : b ≤ a + b := by
    apply Nat.le_add_left
  have h2 : a + b = 0 := h
  rw [h2] at h1
  have h3 : b ≤ 0 := h1
  exact Nat.eq_zero_of_le_zero h3
