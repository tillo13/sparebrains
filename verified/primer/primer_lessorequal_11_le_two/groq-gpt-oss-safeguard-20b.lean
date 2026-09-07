import Mathlib

/-- Natural Number Game (Lean 4), LessOrEqual world, level 11: le_two. Restated over Mathlib's ℕ. Source: https://github.com/leanprover-community/NNG4/blob/main/Game/Levels/LessOrEqual/L11le_two.lean, Apache-2.0. -/
theorem primer_lessorequal_11_le_two (x : ℕ) (hx : x ≤ 2) : x = 0 ∨ x = 1 ∨ x = 2 := by
  have h₁ : x < 2 ∨ x = 2 := Nat.lt_or_eq_of_le hx
  cases h₁ with
  | inl hlt =>
      have hx1 : x ≤ 1 := (Nat.lt_succ_iff).1 hlt
      have h₂ : x < 1 ∨ x = 1 := Nat.lt_or_eq_of_le hx1
      cases h₂ with
      | inl hlt1 =>
          have h0 : x = 0 := (Nat.lt_one_iff).1 hlt1
          exact Or.inl h0
      | inr h1eq =>
          exact Or.inr (Or.inl h1eq)
  | inr h2eq =>
      exact Or.inr (Or.inr h2eq)
