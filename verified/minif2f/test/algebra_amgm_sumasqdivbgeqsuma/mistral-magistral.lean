import Mathlib

open scoped Nat
open scoped Real

theorem algebra_amgm_sumasqdivbgeqsuma (a b c d : ℝ) (h₀ : 0 < a ∧ 0 < b ∧ 0 < c ∧ 0 < d) :
    a ^ 2 / b + b ^ 2 / c + c ^ 2 / d + d ^ 2 / a ≥ a + b + c + d := by
  rcases h₀ with ⟨ha, hb, hc, hd⟩
  have h1 : a ^ 2 / b ≥ 2 * a - b := by
    have h2 : 0 < b := hb
    have h3 : a ^ 2 / b ≥ 2 * a - b := by
      have h4 : 0 < b := hb
      have h5 : a ^ 2 ≥ b * (2 * a - b) := by
        nlinarith [sq_nonneg (a - b)]
      have h6 : a ^ 2 / b ≥ 2 * a - b := by
        apply (le_div_iff₀ (by linarith)).mpr
        linarith
      linarith
    linarith
  have h2 : b ^ 2 / c ≥ 2 * b - c := by
    have h3 : 0 < c := hc
    have h4 : b ^ 2 / c ≥ 2 * b - c := by
      have h5 : b ^ 2 ≥ c * (2 * b - c) := by
        nlinarith [sq_nonneg (b - c)]
      have h6 : b ^ 2 / c ≥ 2 * b - c := by
        apply (le_div_iff₀ (by linarith)).mpr
        linarith
      linarith
    linarith
  have h3 : c ^ 2 / d ≥ 2 * c - d := by
    have h4 : 0 < d := hd
    have h5 : c ^ 2 / d ≥ 2 * c - d := by
      have h6 : c ^ 2 ≥ d * (2 * c - d) := by
        nlinarith [sq_nonneg (c - d)]
      have h7 : c ^ 2 / d ≥ 2 * c - d := by
        apply (le_div_iff₀ (by linarith)).mpr
        linarith
      linarith
    linarith
  have h4 : d ^ 2 / a ≥ 2 * d - a := by
    have h5 : 0 < a := ha
    have h6 : d ^ 2 / a ≥ 2 * d - a := by
      have h7 : d ^ 2 ≥ a * (2 * d - a) := by
        nlinarith [sq_nonneg (d - a)]
      have h8 : d ^ 2 / a ≥ 2 * d - a := by
        apply (le_div_iff₀ (by linarith)).mpr
        linarith
      linarith
    linarith
  linarith
