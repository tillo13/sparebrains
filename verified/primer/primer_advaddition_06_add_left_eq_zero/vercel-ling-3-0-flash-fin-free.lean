import Mathlib

/-- Natural Number Game (Lean 4), AdvAddition world, level 6: add_left_eq_zero. Restated over Mathlib's ℕ. Source: https://github.com/leanprover-community/NNG4/blob/main/Game/Levels/AdvAddition/L06add_left_eq_zero.lean, Apache-2.0. -/
theorem primer_advaddition_06_add_left_eq_zero (a b : ℕ) : a + b = 0 → b = 0 := by
  intro h
  induction' a with a' ih
  · rw [Nat.zero_add] at h
    exact h
  · rw [Nat.succ_add] at h
    exact False.elim (Nat.succ_ne_zero (a' + b) h)
