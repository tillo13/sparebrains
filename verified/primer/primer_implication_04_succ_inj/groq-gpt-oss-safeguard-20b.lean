import Mathlib

/-- Natural Number Game (Lean 4), Implication world, level 4: succ_inj. Restated over Mathlib's ℕ. Source: https://github.com/leanprover-community/NNG4/blob/main/Game/Levels/Implication/L04succ_inj.lean, Apache-2.0. -/
theorem primer_implication_04_succ_inj (x : ℕ) (h : x + 1 = 4) : x = 3 := by
  -- rewrite the hypothesis as a successor equality
  have h' : Nat.succ x = 4 := by
    simpa [Nat.succ_eq_add_one] using h
  -- rewrite 4 as the successor of 3
  have h'' : Nat.succ x = Nat.succ 3 := by
    simpa using h'
  -- use the injectivity of `succ`
  exact Nat.succ_inj.mp h''
