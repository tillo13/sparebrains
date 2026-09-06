import Mathlib

open scoped Nat
open scoped Real

theorem algebra_sqineq_unitcircatbpamblt1 (a b : ℝ) (h₀ : a ^ 2 + b ^ 2 = 1) :
    a * b + (a - b) ≤ 1 := by
  have ha_sq_le : a ^ 2 ≤ (1 : ℝ) := by
    have : a ^ 2 ≤ a ^ 2 + b ^ 2 := by
      have : (0 : ℝ) ≤ b ^ 2 := by exact pow_two_nonneg b
      linarith
    simpa [h₀] using this
  have hb_sq_le : b ^ 2 ≤ (1 : ℝ) := by
    have : b ^ 2 ≤ a ^ 2 + b ^ 2 := by
      have : (0 : ℝ) ≤ a ^ 2 := by exact pow_two_nonneg a
      linarith
    simpa [h₀] using this
  have ha_le_one : a ≤ (1 : ℝ) := by
    nlinarith [ha_sq_le]
  have hb_ge_neg_one : - (1 : ℝ) ≤ b := by
    nlinarith [hb_sq_le]
  have h1a : (0 : ℝ) ≤ 1 - a := sub_nonneg.mpr ha_le_one
  have h1b : (0 : ℝ) ≤ 1 + b := by
    have : -1 ≤ b := hb_ge_neg_one
    linarith
  have h_nonneg : (0 : ℝ) ≤ (1 - a) * (1 + b) := mul_nonneg h1a h1b
  have h_eq : 1 - a * b - a + b = (1 - a) * (1 + b) := by ring
  have : (0 : ℝ) ≤ 1 - a * b - a + b := by
    simpa [h_eq] using h_nonneg
  linarith
