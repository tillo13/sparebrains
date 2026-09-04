import Mathlib

open Real

/-- Mathematics in Lean, Chapter 2 §3 (Using Theorems and Lemmas), exercise 4. Avigad & Massot, Apache-2.0, commit dd6d752. -/
theorem mil_c02_s03_ex04 (a b : ℝ) (h : a ≤ b) : log (1 + exp a) ≤ log (1 + exp b) := by
  have h₁ : 0 < 1 + exp a := add_pos zero_lt_one (exp_pos a)
  have h₂ : 0 < 1 + exp b := add_pos zero_lt_one (exp_pos b)
  have h₃ : exp a ≤ exp b := exp_le_exp.2 h
  have h₄ : 1 + exp a ≤ 1 + exp b := add_le_add (le_rfl) h₃
  exact log_le_log h₁ h₄
