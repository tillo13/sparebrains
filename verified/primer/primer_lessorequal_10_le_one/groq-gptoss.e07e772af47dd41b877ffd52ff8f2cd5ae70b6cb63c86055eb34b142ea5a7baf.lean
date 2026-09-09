import Mathlib

/-- Natural Number Game (Lean 4), LessOrEqual world, level 10: le_one. Restated over Mathlib's ℕ. Source: https://github.com/leanprover-community/NNG4/blob/main/Game/Levels/LessOrEqual/L10le_one.lean, Apache-2.0. -/
theorem primer_lessorequal_10_le_one (x : ℕ) (hx : x ≤ 1) : x = 0 ∨ x = 1 := by
  cases x with
  | zero =>
      exact Or.inl rfl
  | succ y =>
      have h1 : Nat.succ y ≤ 1 := hx
      have h2 : y < 1 := (Nat.succ_le_iff).mp h1
      have h3 : y ≤ 0 := Nat.le_of_lt_succ h2
      have hy : y = 0 := Nat.le_antisymm h3 (Nat.zero_le _)
      have : Nat.succ y = 1 := by simpa [hy]
      exact Or.inr this
