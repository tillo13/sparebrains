import Mathlib

/-- Natural Number Game (Lean 4), LessOrEqual world, level 10: le_one. Restated over Mathlib's ℕ. Source: https://github.com/leanprover-community/NNG4/blob/main/Game/Levels/LessOrEqual/L10le_one.lean, Apache-2.0. -/
theorem primer_lessorequal_10_le_one (x : ℕ) (hx : x ≤ 1) : x = 0 ∨ x = 1 := by
  cases x with
  | zero =>
      left
      rfl
  | succ x' =>
      have hle : Nat.succ x' ≤ 1 := hx
      have hle' : Nat.succ x' ≤ Nat.succ 0 := by
        simpa using hle
      have hx0le : x' ≤ 0 := (Nat.succ_le_succ_iff).mp hle'
      have hx0 : x' = 0 := Nat.le_antisymm hx0le (Nat.zero_le _)
      right
      simpa [hx0]
