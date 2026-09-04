import Mathlib

/-- Natural Number Game (Lean 4), AdvMultiplication world, level 5: le_mul_right. Restated over Mathlib's ℕ. Source: https://github.com/leanprover-community/NNG4/blob/main/Game/Levels/AdvMultiplication/L05le_mul_right.lean, Apache-2.0. -/
theorem primer_advmultiplication_05_le_mul_right (a b : ℕ) (h : a * b ≠ 0) : a ≤ a * b := by
  have h1 : 0 < a := by
    by_contra h0
    push_neg at h0
    have h2 : a = 0 := by omega
    rw [h2] at h
    simp at h
  have h2 : 1 ≤ b := by
    by_contra h0
    push_neg at h0
    have h3 : b = 0 := by omega
    rw [h3] at h
    simp at h
  nlinarith
