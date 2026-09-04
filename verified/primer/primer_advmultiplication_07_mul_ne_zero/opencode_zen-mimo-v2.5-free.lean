import Mathlib

/-- Natural Number Game (Lean 4), AdvMultiplication world, level 7: mul_ne_zero. Restated over Mathlib's ℕ. Source: https://github.com/leanprover-community/NNG4/blob/main/Game/Levels/AdvMultiplication/L07mul_ne_zero.lean, Apache-2.0. -/
theorem primer_advmultiplication_07_mul_ne_zero (a b : ℕ) (ha : a ≠ 0) (hb : b ≠ 0) : a * b ≠ 0 := by
  intro h
  have h1 : a = 0 ∨ b = 0 := by
    rw [Nat.mul_eq_zero] at h
    exact h
  cases h1 with
  | inl h1 => exact ha h1
  | inr h1 => exact hb h1
