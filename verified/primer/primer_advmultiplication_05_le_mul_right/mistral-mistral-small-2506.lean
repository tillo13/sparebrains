import Mathlib

/-- Natural Number Game (Lean 4), AdvMultiplication world, level 5: le_mul_right. Restated over Mathlib's ℕ. Source: https://github.com/leanprover-community/NNG4/blob/main/Game/Levels/AdvMultiplication/L05le_mul_right.lean, Apache-2.0. -/
theorem primer_advmultiplication_05_le_mul_right (a b : ℕ) (h : a * b ≠ 0) : a ≤ a * b := by
  have hb : b ≥ 1 := by
    by_contra h'
    push_neg at h'
    have : b = 0 := by omega
    rw [this] at h
    simp at h
  have : a * b ≥ a * 1 := by
    apply Nat.mul_le_mul_left
    omega
  simp at this
  omega
