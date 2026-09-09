import Mathlib

/-- Natural Number Game (Lean 4), Multiplication world, level 3: succ_mul. Restated over Mathlib's ℕ. Source: https://github.com/leanprover-community/NNG4/blob/main/Game/Levels/Multiplication/L03succ_mul.lean, Apache-2.0. -/
theorem primer_multiplication_03_succ_mul (a b : ℕ) : Nat.succ a * b = a * b + b := by
  induction b with
  | zero => simp [Nat.succ_eq_add_one]
  | succ b ih => 
    calc
      Nat.succ a * (b + 1) = (a + 1) * (b + 1) := rfl
      _ = (a + 1) * b + (a + 1) * 1 := by ring
      _ = (a * b + b) + (a + 1) := by ring
      _ = a * b + b + a + 1 := by ring
      _ = a * (b + 1) + (b + 1) := by ring
