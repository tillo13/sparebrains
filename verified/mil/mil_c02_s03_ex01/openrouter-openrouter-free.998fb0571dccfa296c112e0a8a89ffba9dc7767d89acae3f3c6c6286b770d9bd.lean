import Mathlib

open Real

/-- Mathematics in Lean, Chapter 2 §3 (Using Theorems and Lemmas), exercise 1. Avigad & Massot, Apache-2.0, commit dd6d752. -/
theorem mil_c02_s03_ex01 (a b c d e : ℝ) (h₀ : a ≤ b) (h₁ : b < c) (h₂ : c ≤ d) (h₃ : d < e) : a < e := by
  have h_ac : a < c := by exact lt_of_le_of_lt h₀ h₁
  have h_ad : a < d := by exact lt_of_lt_of_le h_ac h₂
  have h_ae : a < e := by exact lt_trans h_ad h₃
  exact h_ae
