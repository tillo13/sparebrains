import Mathlib

/-- Natural Number Game (Lean 4), AdvMultiplication world, level 5: le_mul_right. Restated over Mathlib's ℕ. Source: https://github.com/leanprover-community/NNG4/blob/main/Game/Levels/AdvMultiplication/L05le_mul_right.lean, Apache-2.0. -/
theorem primer_advmultiplication_05_le_mul_right (a b : ℕ) (h : a * b ≠ 0) : a ≤ a * b := by
  have hb : b ≠ 0 := by
    intro hb
    have : a * b = 0 := by
      rw [hb]
      simp
    contradiction
  have ha : a ≠ 0 := by
    intro ha
    have : a * b = 0 := by
      rw [ha]
      simp
    contradiction
  have h1 : 1 ≤ b := Nat.pos_of_ne_zero hb
  calc
    a = a * 1 := by ring
    _ ≤ a * b := Nat.mul_le_mul_left a h1
