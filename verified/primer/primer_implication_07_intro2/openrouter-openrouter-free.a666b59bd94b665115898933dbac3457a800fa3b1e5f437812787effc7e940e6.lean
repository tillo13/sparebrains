import Mathlib

/-- Natural Number Game (Lean 4), Implication world, level 7: intro practice. Restated over Mathlib's ℕ. Source: https://github.com/leanprover-community/NNG4/blob/main/Game/Levels/Implication/L07intro2.lean, Apache-2.0. -/
theorem primer_implication_07_intro2 (x y : ℕ) : x + 1 = y + 1 → x = y := by
  intro h
  have h₁ : x = y := by
    -- Use the cancellation property of addition on the right to deduce x = y from x + 1 = y + 1
    apply Nat.add_right_cancel h
  exact h₁
