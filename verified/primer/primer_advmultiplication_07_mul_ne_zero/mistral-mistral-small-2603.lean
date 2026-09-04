import Mathlib

/-- Natural Number Game (Lean 4), AdvMultiplication world, level 7: mul_ne_zero. Restated over Mathlib's ℕ. Source: https://github.com/leanprover-community/NNG4/blob/main/Game/Levels/AdvMultiplication/L07mul_ne_zero.lean, Apache-2.0. -/
theorem primer_advmultiplication_07_mul_ne_zero (a b : ℕ) (ha : a ≠ 0) (hb : b ≠ 0) : a * b ≠ 0 := by
  intro h
  have h1 : a = 0 ∨ b = 0 := by
    rcases Nat.eq_zero_or_pos a with (r | _) <;> rcases Nat.eq_zero_or_pos b with (r | _) <;>
      simp_all [Nat.mul_eq_zero]
  tauto
