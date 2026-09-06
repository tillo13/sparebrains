import Mathlib

/-- Natural Number Game (Lean 4), Implication world, level 4: succ_inj. Restated over Mathlib's ℕ. Source: https://github.com/leanprover-community/NNG4/blob/main/Game/Levels/Implication/L04succ_inj.lean, Apache-2.0. -/
theorem primer_implication_04_succ_inj (x : ℕ) (h : x + 1 = 4) : x = 3 := by
  have h' : Nat.succ x = 4 := by
    simpa [Nat.succ_eq_add_one] using h
  -- Now we want to deduce x = 3. Use Nat.succ_eq_add_one? Actually we can rewrite 4 as 3.succ
  have : Nat.succ x = Nat.succ 3 := by
    simpa [Nat.succ_eq_add_one] using h
  -- Then use Nat.succ_inj
  exact Nat.succ_inj.mp this
