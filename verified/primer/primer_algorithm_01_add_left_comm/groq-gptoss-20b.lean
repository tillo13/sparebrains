import Mathlib

/-- Natural Number Game (Lean 4), Algorithm world, level 1: add_left_comm. Restated over Mathlib's ℕ. Source: https://github.com/leanprover-community/NNG4/blob/main/Game/Levels/Algorithm/L01add_left_comm.lean, Apache-2.0. -/
theorem primer_algorithm_01_add_left_comm (a b c : ℕ) : a + (b + c) = b + (a + c) := by
  calc
    a + (b + c) = (a + b) + c := by
      simpa using (Nat.add_assoc a b c).symm
    _ = (b + a) + c := by
      simpa [Nat.add_comm]
    _ = b + (a + c) := by
      simpa using (Nat.add_assoc b a c)
