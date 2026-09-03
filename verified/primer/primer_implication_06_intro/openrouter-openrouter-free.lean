import Mathlib

/-- Natural Number Game (Lean 4), Implication world, level 6: intro. Restated over Mathlib's ℕ. Source: https://github.com/leanprover-community/NNG4/blob/main/Game/Levels/Implication/L06intro.lean, Apache-2.0. -/
theorem primer_implication_06_intro (x : ℕ) : x = 37 → x = 37 := by
  intro h
  have h₁ : x = 37 := by
    -- The hypothesis `h` directly gives us `x = 37`, so we can use it to close the goal.
    exact h
  -- The final goal is `x = 37`, which is exactly `h₁`.
  exact h₁
