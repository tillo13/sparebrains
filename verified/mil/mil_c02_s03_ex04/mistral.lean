import Mathlib

open Real

/-- Mathematics in Lean, Chapter 2 §3 (Using Theorems and Lemmas), exercise 4. Avigad & Massot, Apache-2.0, commit dd6d752. -/
theorem mil_c02_s03_ex04 (a b : ℝ) (h : a ≤ b) : log (1 + exp a) ≤ log (1 + exp b) := by
  have h1 : exp a ≤ exp b := by
    apply Real.exp_le_exp_of_le
    linarith
  have h2 : (1 + exp a : ℝ) ≤ (1 + exp b : ℝ) := by
    linarith [h1]
  have h3 : (0 : ℝ) < 1 + exp a := by
    positivity
  have h4 : (0 : ℝ) < 1 + exp b := by
    positivity
  apply Real.log_le_log
  all_goals linarith [h2, h3, h4]
