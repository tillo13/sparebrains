import Mathlib

/-- Natural Number Game (Lean 4), LessOrEqual world, level 10: le_one. Restated over Mathlib's ℕ. Source: https://github.com/leanprover-community/NNG4/blob/main/Game/Levels/LessOrEqual/L10le_one.lean, Apache-2.0. -/
theorem primer_lessorequal_10_le_one (x : ℕ) (hx : x ≤ 1) : x = 0 ∨ x = 1 := by
  have h_main : x = 0 ∨ x = 1 := by
    have h₁ : x ≤ 1 := hx
    have h₂ : x = 0 ∨ x = 1 := by
      -- We use the fact that x is a natural number and x ≤ 1 to deduce that x must be 0 or 1.
      have h₃ : x ≤ 1 := h₁
      -- We consider the possible values of x.
      have h₄ : x = 0 ∨ x = 1 := by
        -- We use the fact that x is a natural number and x ≤ 1 to deduce that x must be 0 or 1.
        interval_cases x <;> simp_all (config := {decide := true})
      exact h₄
    exact h₂
  exact h_main
