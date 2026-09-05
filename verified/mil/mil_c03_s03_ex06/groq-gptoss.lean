import Mathlib

/-- Mathematics in Lean, Chapter 3 §3 (Negation), exercise 6. Avigad & Massot, Apache-2.0, commit dd6d752. -/
theorem mil_c03_s03_ex06 (x : ℝ) (h : ∀ ε > 0, x < ε) : x ≤ 0 := by
  by_contra hxle
  have hxpos : 0 < x := lt_of_not_ge hxle
  have hpos : 0 < x / 2 := half_pos hxpos
  have hlt : x < x / 2 := h _ hpos
  have hlt' : x / 2 < x := half_lt_self hxpos
  exact (lt_asymm hlt hlt')
