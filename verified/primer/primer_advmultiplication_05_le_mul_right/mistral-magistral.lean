import Mathlib

/-- Natural Number Game (Lean 4), AdvMultiplication world, level 5: le_mul_right. Restated over Mathlib's ℕ. Source: https://github.com/leanprover-community/NNG4/blob/main/Game/Levels/AdvMultiplication/L05le_mul_right.lean, Apache-2.0. -/
theorem primer_advmultiplication_05_le_mul_right (a b : ℕ) (h : a * b ≠ 0) : a ≤ a * b := by
  have hb : b ≥ 1 := by
    by_contra h'
    push_neg at h'
    have h'' : b = 0 := by omega
    rw [h''] at h
    simp at h
  have h1 : a * b ≥ a * 1 := by
    nlinarith [hb]
  have h2 : a * 1 = a := by
    simp
  linarith [h1, h2]
