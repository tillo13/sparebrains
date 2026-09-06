import Mathlib

/-- Natural Number Game (Lean 4), LessOrEqual world, level 11: le_two. Restated over Mathlib's ℕ. Source: https://github.com/leanprover-community/NNG4/blob/main/Game/Levels/LessOrEqual/L11le_two.lean, Apache-2.0. -/
theorem primer_lessorequal_11_le_two (x : ℕ) (hx : x ≤ 2) : x = 0 ∨ x = 1 ∨ x = 2 := by
  rcases Nat.lt_or_eq_of_le hx with hlt | rfl
  · have hle1 : x ≤ 1 := Nat.le_of_lt_succ hlt
    rcases Nat.lt_or_eq_of_le hle1 with hlt1 | rfl
    · exact Or.inl (Nat.lt_one_iff.mp hlt1)
    · exact Or.inr (Or.inl rfl)
  · exact Or.inr (Or.inr rfl)
