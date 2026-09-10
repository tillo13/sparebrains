import Mathlib

open Real

/-- Mathematics in Lean, Chapter 2 §3 (Using Theorems and Lemmas), exercise 4. Avigad & Massot, Apache-2.0, commit dd6d752. -/
theorem mil_c02_s03_ex04 (a b : ℝ) (h : a ≤ b) : log (1 + exp a) ≤ log (1 + exp b) := by
  have h1 : exp a ≤ exp b := exp_le_exp.mpr h
  have h2 : exp a + 1 ≤ exp b + 1 := add_le_add_left h1 1
  have h3 : 0 < 1 + exp a := by
    have : 0 < exp a := exp_pos a
    linarith
  have h4 : 1 + exp a ≤ 1 + exp b := by
    rw [add_comm (exp a) 1, add_comm (exp b) 1] at h2
    exact h2
  exact log_le_log h3 h4
