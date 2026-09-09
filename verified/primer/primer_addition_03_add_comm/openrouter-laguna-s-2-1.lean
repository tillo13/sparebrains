import Mathlib

/-- Natural Number Game (Lean 4), Addition world, level 3: add_comm (level boss). Restated over Mathlib's ℕ. Source: https://github.com/leanprover-community/NNG4/blob/main/Game/Levels/Addition/L03add_comm.lean, Apache-2.0. -/
theorem primer_addition_03_add_comm (a b : ℕ) : a + b = b + a := by
  induction a with
  | zero =>
    show 0 + b = b + 0
    rw [Nat.add_zero, Nat.zero_add]
  | succ a ih =>
    show (a + 1) + b = b + (a + 1)
    rw [Nat.succ_add, Nat.add_succ, ih]
