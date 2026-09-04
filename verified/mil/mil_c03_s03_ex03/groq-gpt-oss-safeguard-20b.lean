import Mathlib

/-- Mathematics in Lean, Chapter 3 §3 (Negation), exercise 3. Avigad & Massot, Apache-2.0, commit dd6d752. -/
theorem mil_c03_s03_ex03 (a b : ℝ) (f : ℝ → ℝ) (h : Monotone f) (h' : f a < f b) : a < b := by
  -- First show `a ≤ b`
  have hle : a ≤ b := by
    by_contra hnot
    have hlt : b < a := lt_of_not_ge hnot
    have hle' : f b ≤ f a := h hlt.le
    have : f a < f a := lt_of_lt_of_le h' hle'
    exact lt_irrefl _ this
  -- Then show `a ≠ b`
  have hne : a ≠ b := by
    intro h_eq
    have : f a < f a := by simpa [h_eq] using h'
    exact lt_irrefl _ this
  -- Conclude `a < b`
  exact lt_of_le_of_ne hle hne
