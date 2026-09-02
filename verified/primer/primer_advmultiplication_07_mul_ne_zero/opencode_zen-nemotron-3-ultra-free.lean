import Mathlib

/-- Natural Number Game (Lean 4), AdvMultiplication world, level 7: mul_ne_zero. Restated over Mathlib's ℕ. Source: https://github.com/leanprover-community/NNG4/blob/main/Game/Levels/AdvMultiplication/L07mul_ne_zero.lean, Apache-2.0. -/
theorem primer_advmultiplication_07_mul_ne_zero (a b : ℕ) (ha : a ≠ 0) (hb : b ≠ 0) : a * b ≠ 0 := by
  have h_main : a * b ≠ 0 := by
    intro h
    have h₁ : a = 0 ∨ b = 0 := by
      -- Use the property that if the product of two natural numbers is zero, then at least one of them is zero.
      have h₂ : a * b = 0 := h
      have h₃ : a = 0 ∨ b = 0 := by
        -- Apply the lemma `Nat.mul_eq_zero` which states that `a * b = 0 ↔ a = 0 ∨ b = 0`.
        simpa [Nat.mul_eq_zero] using h₂
      exact h₃
    -- Now we have `a = 0 ∨ b = 0`, but we know `a ≠ 0` and `b ≠ 0`, so we derive a contradiction.
    cases h₁ with
    | inl h₁ =>
      -- Case: `a = 0`
      apply ha
      exact h₁
    | inr h₁ =>
      -- Case: `b = 0`
      apply hb
      exact h₁
  exact h_main
