import Mathlib

open scoped Nat
open scoped Real

theorem algebra_amgm_sumasqdivbgeqsuma (a b c d : ℝ) (h₀ : 0 < a ∧ 0 < b ∧ 0 < c ∧ 0 < d) :
    a ^ 2 / b + b ^ 2 / c + c ^ 2 / d + d ^ 2 / a ≥ a + b + c + d := by
  rcases h₀ with ⟨ha, hb, hc, hd⟩
  have h₁ : a ^ 2 / b + b ≥ 2 * a := by
    have h₁₀ : 0 ≤ (a - b) ^ 2 / b := by positivity
    have h₁₁ : a ^ 2 / b - 2 * a + b = (a - b) ^ 2 / b := by
      field_simp [hb.ne']
      ring
    linarith
  have h₂ : b ^ 2 / c + c ≥ 2 * b := by
    have h₂₀ : 0 ≤ (b - c) ^ 2 / c := by positivity
    have h₂₁ : b ^ 2 / c - 2 * b + c = (b - c) ^ 2 / c := by
      field_simp [hc.ne']
      ring
    linarith
  have h₃ : c ^ 2 / d + d ≥ 2 * c := by
    have h₃₀ : 0 ≤ (c - d) ^ 2 / d := by positivity
    have h₃₁ : c ^ 2 / d - 2 * c + d = (c - d) ^ 2 / d := by
      field_simp [hd.ne']
      ring
    linarith
  have h₄ : d ^ 2 / a + a ≥ 2 * d := by
    have h₄₀ : 0 ≤ (d - a) ^ 2 / a := by positivity
    have h₄₁ : d ^ 2 / a - 2 * d + a = (d - a) ^ 2 / a := by
      field_simp [ha.ne']
      ring
    linarith
  linarith
