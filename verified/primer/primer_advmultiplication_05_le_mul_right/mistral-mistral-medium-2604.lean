import Mathlib

/-- Natural Number Game (Lean 4), AdvMultiplication world, level 5: le_mul_right. Restated over Mathlib's ℕ. Source: https://github.com/leanprover-community/NNG4/blob/main/Game/Levels/AdvMultiplication/L05le_mul_right.lean, Apache-2.0. -/
theorem primer_advmultiplication_05_le_mul_right (a b : ℕ) (h : a * b ≠ 0) : a ≤ a * b := by
  have hb : b ≠ 0 := by
    by_contra hb'
    rw [hb'] at h
    simp at h
  have ha : a ≠ 0 := by
    by_contra ha'
    rw [ha'] at h
    simp at h
  have hb_pos : 0 < b := Nat.pos_of_ne_zero hb
  have ha_pos : 0 < a := Nat.pos_of_ne_zero ha
  nlinarith
