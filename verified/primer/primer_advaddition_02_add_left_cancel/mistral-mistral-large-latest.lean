import Mathlib

/-- Natural Number Game (Lean 4), AdvAddition world, level 2: add_left_cancel. Restated over Mathlib's ℕ. Source: https://github.com/leanprover-community/NNG4/blob/main/Game/Levels/AdvAddition/L02add_left_cancel.lean, Apache-2.0. -/
theorem primer_advaddition_02_add_left_cancel (a b n : ℕ) : n + a = n + b → a = b := by
  induction n with
  | zero => intro h; rw [Nat.zero_add, Nat.zero_add] at h; exact h
  | succ n ih => intro h; apply ih; rw [Nat.succ_add, Nat.succ_add] at h; exact Nat.succ.inj h
