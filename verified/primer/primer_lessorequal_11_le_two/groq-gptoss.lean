import Mathlib

/-- Natural Number Game (Lean 4), LessOrEqual world, level 11: le_two. Restated over Mathlib's ℕ. Source: https://github.com/leanprover-community/NNG4/blob/main/Game/Levels/LessOrEqual/L11le_two.lean, Apache-2.0. -/
theorem primer_lessorequal_11_le_two (x : ℕ) (hx : x ≤ 2) : x = 0 ∨ x = 1 ∨ x = 2 := by
  cases x with
  | zero =>
      exact Or.inl rfl
  | succ x1 =>
      have hx1 : Nat.succ x1 ≤ 2 := hx
      cases x1 with
      | zero =>
          exact Or.inr <| Or.inl rfl
      | succ x2 =>
          have h2 : Nat.succ (Nat.succ x2) ≤ 2 := hx1
          -- From `succ (succ x2) ≤ 2` we get `succ x2 ≤ 1`.
          have h1 : Nat.succ x2 ≤ 1 := by
            have : Nat.succ x2 < 2 := (Nat.succ_le_iff.mp h2)
            have : Nat.succ x2 < Nat.succ 1 := by simpa using this
            exact (Nat.lt_succ_iff).mp this
          -- From `succ x2 ≤ 1` we get `x2 = 0`.
          have h0 : x2 = 0 := by
            have : x2 < 1 := (Nat.succ_le_iff.mp h1)
            exact (Nat.lt_one_iff).mp this
          exact Or.inr <| Or.inr (by
            simpa [h0] )
