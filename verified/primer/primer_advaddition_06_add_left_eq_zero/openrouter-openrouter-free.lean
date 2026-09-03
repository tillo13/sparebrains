import Mathlib

/-- Natural Number Game (Lean 4), AdvAddition world, level 6: add_left_eq_zero. Restated over Mathlib's ℕ. Source: https://github.com/leanprover-community/NNG4/blob/main/Game/Levels/AdvAddition/L06add_left_eq_zero.lean, Apache-2.0. -/
theorem primer_advaddition_06_add_left_eq_zero (a b : ℕ) : a + b = 0 → b = 0 := by
  intro h
  have h₁ : a = 0 ∧ b = 0 := by
    have h₂ : a + b = 0 := h
    have h₃ : a = 0 ∧ b = 0 := by
      -- Use the property that the sum of two natural numbers is zero if and only if both are zero.
      have h₄ : a + b = 0 := h₂
      have h₅ : a = 0 ∧ b = 0 := by
        -- Apply the lemma that characterizes when the sum of two natural numbers is zero.
        rw [Nat.add_eq_zero] at h₄
        exact h₄
      exact h₅
    exact h₃
  
  have h₂ : b = 0 := by
    -- Extract the second part of the conjunction to get b = 0.
    have h₃ : a = 0 ∧ b = 0 := h₁
    have h₄ : b = 0 := h₃.2
    exact h₄
  
  exact h₂
