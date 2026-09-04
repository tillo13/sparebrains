import Mathlib

/-- Mathematics in Lean, Chapter 3 §3 (Negation), exercise 6. Avigad & Massot, Apache-2.0, commit dd6d752. -/
theorem mil_c03_s03_ex06 (x : ℝ) (h : ∀ ε > 0, x < ε) : x ≤ 0 := by
  by_contra hx
  have hxpos : 0 < x := lt_of_not_ge hx
  have hpos : 0 < x / 2 := by
    have : (0 : ℝ) < (2 : ℝ) := by norm_num
    exact div_pos hxpos this
  have hlt : x < x / 2 := h (x / 2) hpos
  have : x < x := lt_trans hlt (half_lt_self hxpos)
  exact lt_irrefl _ this
