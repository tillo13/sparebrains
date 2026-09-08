import Mathlib

/-- Natural Number Game (Lean 4), LessOrEqual world, level 11: le_two. Restated over Mathlib's ℕ. Source: https://github.com/leanprover-community/NNG4/blob/main/Game/Levels/LessOrEqual/L11le_two.lean, Apache-2.0. -/
theorem primer_lessorequal_11_le_two (x : ℕ) (hx : x ≤ 2) : x = 0 ∨ x = 1 ∨ x = 2 := by
  rcases lt_or_eq_of_le hx with hlt | h_eq
  · -- case `x < 2`
    have hle1 : x ≤ 1 := (Nat.lt_succ_iff).1 hlt
    rcases lt_or_eq_of_le hle1 with hlt' | h_eq'
    · -- case `x < 1`
      have h0 : x = 0 := (Nat.lt_one_iff).1 hlt'
      exact Or.inl h0
    · -- case `x = 1`
      exact Or.inr (Or.inl h_eq')
  · -- case `x = 2`
    exact Or.inr (Or.inr h_eq)
