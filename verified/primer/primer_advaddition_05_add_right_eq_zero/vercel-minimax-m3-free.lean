import Mathlib

/-- Natural Number Game (Lean 4), AdvAddition world, level 5: add_right_eq_zero. Restated over Mathlib's ℕ. Source: https://github.com/leanprover-community/NNG4/blob/main/Game/Levels/AdvAddition/L05add_right_eq_zero.lean, Apache-2.0. -/
theorem primer_advaddition_05_add_right_eq_zero (a b : ℕ) : a + b = 0 → a = 0 := by
  intro h
  have hab : a ≤ a + b := Nat.le_add_right _ _
  rw [h] at hab
  exact Nat.le_zero.mp hab
