import Mathlib

/-- Natural Number Game (Lean 4), Multiplication world, level 7: mul_add. Restated over Mathlib's ℕ. Source: https://github.com/leanprover-community/NNG4/blob/main/Game/Levels/Multiplication/L07mul_add.lean, Apache-2.0. -/
theorem primer_multiplication_07_mul_add (a b c : ℕ) : a * (b + c) = a * b + a * c := by
  induction c with
  | zero => simp [mul_zero]
  | succ c ih =>
    rw [Nat.add_succ, Nat.mul_succ, ih, Nat.mul_succ, Nat.add_assoc]
