import Mathlib

open scoped Nat
open scoped Real

/--
What digit must be placed in the blank to make the four-digit integer $20\_7$ a multiple of 11? -/
theorem mathd_numbertheory_293 (n : ℕ) (h₀ : n ≤ 9) (h₁ : 11 ∣ 20 * 100 + 10 * n + 7) : n = 5 := by
  -- Simplify the expression
  have h₂ : 20 * 100 = 2000 := by omega
  rw [h₂, show 2000 + 10 * n + 7 = 2007 + 10 * n from by ring] at h₁
  -- Now h₁ : 11 ∣ 2007 + 10 * n
  have h₃ : (2007 + 10 * n) % 11 = 0 := Nat.mod_eq_zero_of_dvd h₁
  -- Now case analysis on n
  interval_cases n <;> norm_num at h₃ <;> try exact rfl
  -- For n=5, h₃ is true, goal is 5=5, so exact rfl works.
  -- For other n, h₃ becomes a false statement like 7 % 11 = 0, so we can use contradiction.
  all_goals contradiction
