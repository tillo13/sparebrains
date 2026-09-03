import Mathlib

/-- Mathematics in Lean, Chapter 3 §3 (Negation), exercise 4. Avigad & Massot, Apache-2.0, commit dd6d752. -/
theorem mil_c03_s03_ex04 (a b : ℝ) (f : ℝ → ℝ) (h : a ≤ b) (h' : f b < f a) : ¬Monotone f := by
  intro hf
  have hle : f a ≤ f b := hf h
  have hlt : f a < f a := lt_of_le_of_lt hle h'
  exact lt_irrefl _ hlt
