import Mathlib

/-- Natural Number Game (Lean 4), LessOrEqual world, level 10: le_one. Restated over Mathlib's ℕ. Source: https://github.com/leanprover-community/NNG4/blob/main/Game/Levels/LessOrEqual/L10le_one.lean, Apache-2.0. -/
theorem primer_lessorequal_10_le_one (x : ℕ) (hx : x ≤ 1) : x = 0 ∨ x = 1 := by
  cases x with
  | zero =>
      left; rfl
  | succ x =>
      have h' : x < 1 := by
        exact (Nat.succ_le_iff).mp hx
      have hx0 : x = 0 := (Nat.lt_one_iff).1 h'
      right
      simpa [hx0]
