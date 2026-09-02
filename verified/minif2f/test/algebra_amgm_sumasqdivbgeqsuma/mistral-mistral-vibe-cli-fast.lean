import Mathlib

open scoped Nat
open scoped Real

theorem algebra_amgm_sumasqdivbgeqsuma (a b c d : ℝ) (h₀ : 0 < a ∧ 0 < b ∧ 0 < c ∧ 0 < d) :
    a ^ 2 / b + b ^ 2 / c + c ^ 2 / d + d ^ 2 / a ≥ a + b + c + d := by
  rcases h₀ with ⟨ha, hb, hc, hd⟩
  have h1 : a ^ 2 / b ≥ 2 * a - b := by
    have h2 : 0 < b := hb
    have h3 : a ^ 2 / b - (2 * a - b) ≥ 0 := by
      have h4 : a ^ 2 / b - (2 * a - b) = (a ^ 2 - 2 * a * b + b ^ 2) / b := by
        field_simp
        ring
      rw [h4]
      have h5 : a ^ 2 - 2 * a * b + b ^ 2 = (a - b) ^ 2 := by ring
      rw [h5]
      have h6 : (a - b) ^ 2 ≥ 0 := by apply sq_nonneg
      have h7 : (a - b) ^ 2 / b ≥ 0 := by positivity
      linarith
    linarith
  have h2 : b ^ 2 / c ≥ 2 * b - c := by
    have h2 : 0 < c := hc
    have h3 : b ^ 2 / c - (2 * b - c) ≥ 0 := by
      have h4 : b ^ 2 / c - (2 * b - c) = (b ^ 2 - 2 * b * c + c ^ 2) / c := by
        field_simp
        ring
      rw [h4]
      have h5 : b ^ 2 - 2 * b * c + c ^ 2 = (b - c) ^ 2 := by ring
      rw [h5]
      have h6 : (b - c) ^ 2 ≥ 0 := by apply sq_nonneg
      have h7 : (b - c) ^ 2 / c ≥ 0 := by positivity
      linarith
    linarith
  have h3 : c ^ 2 / d ≥ 2 * c - d := by
    have h2 : 0 < d := hd
    have h3 : c ^ 2 / d - (2 * c - d) ≥ 0 := by
      have h4 : c ^ 2 / d - (2 * c - d) = (c ^ 2 - 2 * c * d + d ^ 2) / d := by
        field_simp
        ring
      rw [h4]
      have h5 : c ^ 2 - 2 * c * d + d ^ 2 = (c - d) ^ 2 := by ring
      rw [h5]
      have h6 : (c - d) ^ 2 ≥ 0 := by apply sq_nonneg
      have h7 : (c - d) ^ 2 / d ≥ 0 := by positivity
      linarith
    linarith
  have h4 : d ^ 2 / a ≥ 2 * d - a := by
    have h2 : 0 < a := ha
    have h3 : d ^ 2 / a - (2 * d - a) ≥ 0 := by
      have h4 : d ^ 2 / a - (2 * d - a) = (d ^ 2 - 2 * d * a + a ^ 2) / a := by
        field_simp
        ring
      rw [h4]
      have h5 : d ^ 2 - 2 * d * a + a ^ 2 = (d - a) ^ 2 := by ring
      rw [h5]
      have h6 : (d - a) ^ 2 ≥ 0 := by apply sq_nonneg
      have h7 : (d - a) ^ 2 / a ≥ 0 := by positivity
      linarith
    linarith
  linarith
