import Mathlib

open Real

/-- Mathematics in Lean, Chapter 2 §3 (Using Theorems and Lemmas), exercise 4. Avigad & Massot, Apache-2.0, commit dd6d752. -/
theorem mil_c02_s03_ex04 (a b : ℝ) (h : a ≤ b) : log (1 + exp a) ≤ log (1 + exp b) := by
  have h₁ : 0 < 1 + exp a := by
    positivity
  have h₂ : 0 < 1 + exp b := by
    positivity
  have h₃ : 1 + exp a ≤ 1 + exp b := by
    have h₄ : exp a ≤ exp b := by
      apply Real.exp_le_exp_of_le
      linarith
    linarith
  apply Real.log_le_log
  all_goals linarith
