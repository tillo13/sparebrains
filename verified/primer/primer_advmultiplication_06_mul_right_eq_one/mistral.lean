import Mathlib

/-- Natural Number Game (Lean 4), AdvMultiplication world, level 6: mul_right_eq_one. Restated over Mathlib's ℕ. Source: https://github.com/leanprover-community/NNG4/blob/main/Game/Levels/AdvMultiplication/L06mul_right_eq_one.lean, Apache-2.0. -/
theorem primer_advmultiplication_06_mul_right_eq_one (x y : ℕ) (h : x * y = 1) : x = 1 := by
  have h1 : x * y = 1 := h
  have h2 : x ≠ 0 := by
    intro h0
    rw [h0] at h1
    simp at h1
  have h3 : y ≠ 0 := by
    intro h0
    rw [h0] at h1
    simp at h1
  have h4 : x = 1 := by
    have h5 : x * y = 1 := h1
    have h6 : y = 1 := by
      have h7 : x * y = 1 := h5
      have h8 : x ≥ 1 := by omega
      have h9 : y ≥ 1 := by omega
      have h10 : x ≤ 1 := by
        nlinarith
      have h11 : y ≤ 1 := by
        nlinarith
      interval_cases x <;> interval_cases y <;> omega
    rw [h6] at h5
    simp at h5
    all_goals omega
  exact h4
