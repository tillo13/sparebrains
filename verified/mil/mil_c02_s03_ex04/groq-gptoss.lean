import Mathlib

open Real

/-- Mathematics in Lean, Chapter 2 §3 (Using Theorems and Lemmas), exercise 4. Avigad & Massot, Apache-2.0, commit dd6d752. -/
theorem mil_c02_s03_ex04 (a b : ℝ) (h : a ≤ b) : log (1 + exp a) ≤ log (1 + exp b) := by
  have h_exp : exp a ≤ exp b := (Real.exp_le_exp).2 h
  have h_add : 1 + exp a ≤ 1 + exp b := by
    simpa using add_le_add_left h_exp 1
  have h_pos : 0 < 1 + exp a := by
    have h0 : (0 : ℝ) < 1 := by norm_num
    have hexp : 0 ≤ exp a := Real.exp_nonneg a
    linarith
  exact Real.log_le_log h_pos h_add
