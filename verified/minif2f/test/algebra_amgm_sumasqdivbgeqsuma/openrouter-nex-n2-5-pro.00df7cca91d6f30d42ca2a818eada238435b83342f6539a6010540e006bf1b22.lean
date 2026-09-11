import Mathlib

open scoped Nat
open scoped Real

theorem algebra_amgm_sumasqdivbgeqsuma (a b c d : ℝ) (h₀ : 0 < a ∧ 0 < b ∧ 0 < c ∧ 0 < d) :
    a ^ 2 / b + b ^ 2 / c + c ^ 2 / d + d ^ 2 / a ≥ a + b + c + d := by
  have ha : 0 < a := h₀.1
  have hb : 0 < b := h₀.2.1
  have hc : 0 < c := h₀.2.2.1
  have hd : 0 < d := h₀.2.2.2
  have h₁ :
      a ^ 2 / b + b ^ 2 / c + c ^ 2 / d + d ^ 2 / a - (a + b + c + d) =
        (a - b) ^ 2 / b + (b - c) ^ 2 / c + (c - d) ^ 2 / d + (d - a) ^ 2 / a := by
    field_simp [ha.ne', hb.ne', hc.ne', hd.ne']
    ring
  have h₂ :
      0 ≤ (a - b) ^ 2 / b + (b - c) ^ 2 / c + (c - d) ^ 2 / d + (d - a) ^ 2 / a := by
    positivity
  linarith [h₁, h₂]
