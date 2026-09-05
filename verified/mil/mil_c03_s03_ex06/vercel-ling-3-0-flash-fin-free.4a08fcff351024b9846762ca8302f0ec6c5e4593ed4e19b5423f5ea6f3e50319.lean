import Mathlib

/-- Mathematics in Lean, Chapter 3 §3 (Negation), exercise 6. Avigad & Massot, Apache-2.0, commit dd6d752. -/
theorem mil_c03_s03_ex06 (x : ℝ) (h : ∀ ε > 0, x < ε) : x ≤ 0 := by
  by_contra hx
  have hε : 0 < x / 2 := by linarith [not_le.mp hx]
  have : x < x / 2 := h (x / 2) hε
  have : x / 2 < x := by linarith [hε]  -- from 0 < x, we get x/2 < x
  linarith [this, this]  -- wait, this doesn't make sense
