import Mathlib

open scoped Nat
open scoped Real

theorem algebra_amgm_sumasqdivbgeqsuma (a b c d : ℝ) (h₀ : 0 < a ∧ 0 < b ∧ 0 < c ∧ 0 < d) :
    a ^ 2 / b + b ^ 2 / c + c ^ 2 / d + d ^ 2 / a ≥ a + b + c + d := by
  rcases h₀ with ⟨ha, hb, hc, hd⟩
  have h1 : a ^ 2 / b ≥ 2 * a - b := by
    have h2 : 0 < b := hb
    apply (le_div_iff₀ (by linarith)).mpr
    nlinarith [sq_nonneg (a - b)]
  have h2 : b ^ 2 / c ≥ 2 * b - c := by
    have h3 : 0 < c := hc
    apply (le_div_iff₀ (by linarith)).mpr
    nlinarith [sq_nonneg (b - c)]
  have h3 : c ^ 2 / d ≥ 2 * c - d := by
    have h4 : 0 < d := hd
    apply (le_div_iff₀ (by linarith)).mpr
    nlinarith [sq_nonneg (c - d)]
  have h4 : d ^ 2 / a ≥ 2 * d - a := by
    have h5 : 0 < a := ha
    apply (le_div_iff₀ (by linarith)).mpr
    nlinarith [sq_nonneg (d - a)]
  linarith
