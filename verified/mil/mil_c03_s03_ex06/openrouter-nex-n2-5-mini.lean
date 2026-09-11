import Mathlib

/-- Mathematics in Lean, Chapter 3 §3 (Negation), exercise 6. Avigad & Massot, Apache-2.0, commit dd6d752. -/
theorem mil_c03_s03_ex06 (x : ℝ) (h : ∀ ε > 0, x < ε) : x ≤ 0 := by
  by_contra hx
  have hx' : 0 < x := lt_of_not_ge hx
  have hε : 0 < x / 2 := by linarith
  have h₁ : x < x / 2 := h (x / 2) hε
  linarith
