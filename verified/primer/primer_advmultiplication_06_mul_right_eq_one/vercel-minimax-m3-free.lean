import Mathlib

/-- Natural Number Game (Lean 4), AdvMultiplication world, level 6: mul_right_eq_one. Restated over Mathlib's ℕ. Source: https://github.com/leanprover-community/NNG4/blob/main/Game/Levels/AdvMultiplication/L06mul_right_eq_one.lean, Apache-2.0. -/
theorem primer_advmultiplication_06_mul_right_eq_one (x y : ℕ) (h : x * y = 1) : x = 1 := by
  cases x with
  | zero => simp at h
  | succ x' =>
    cases y with
    | zero => simp at h
    | succ y' =>
      have : (x' + 1) * (y' + 1) = 1 := by simpa using h
      rw [mul_add, add_mul, one_mul, mul_one, ← add_assoc] at this
      omega
