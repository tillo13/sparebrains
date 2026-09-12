import Mathlib

/-- Mathematics in Lean, Chapter 3 §3 (Negation), exercise 6. Avigad & Massot, Apache-2.0, commit dd6d752. -/
theorem mil_c03_s03_ex06 (x : ℝ) (h : ∀ ε > 0, x < ε) : x ≤ 0 := by
  by_contra hnot
  have hxpos : 0 < x := lt_of_not_ge hnot
  have hε : x / 2 > 0 := by linarith
  have hlt : x < x / 2 := h (x / 2) hε
  linarith
