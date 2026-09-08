import Mathlib

/-- Natural Number Game (Lean 4), Implication world, level 7: intro practice. Restated over Mathlib's ℕ. Source: https://github.com/leanprover-community/NNG4/blob/main/Game/Levels/Implication/L07intro2.lean, Apache-2.0. -/
theorem primer_implication_07_intro2 (x y : ℕ) : x + 1 = y + 1 → x = y := by
  intro h
  have h_main : x = y := by
    -- Use the cancellation property of addition to deduce x = y from x + 1 = y + 1
    have h₁ : x + 1 = y + 1 := h
    -- Apply the lemma Nat.add_right_cancel to cancel 1 from both sides
    have h₂ : x = y := by
      apply Nat.add_right_cancel h₁
    exact h₂
  exact h_main
