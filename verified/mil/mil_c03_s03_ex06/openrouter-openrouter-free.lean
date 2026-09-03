import Mathlib

/-- Mathematics in Lean, Chapter 3 §3 (Negation), exercise 6. Avigad & Massot, Apache-2.0, commit dd6d752. -/
theorem mil_c03_s03_ex06 (x : ℝ) (h : ∀ ε > 0, x < ε) : x ≤ 0 := by
  have h_main : x ≤ 0 := by
    by_contra h₁
    -- Assume x > 0 and derive a contradiction
    have h₂ : x > 0 := by linarith
    -- Apply the given condition with ε = x
    have h₃ : x < x := by
      have h₄ : x > 0 := h₂
      have h₅ : x < x := by
        -- Use the hypothesis with ε = x
        have h₆ : x > 0 := h₄
        have h₇ : x < x := by
          specialize h x (by linarith)
          linarith
        exact h₇
      exact h₅
    -- Contradiction: x < x is false
    linarith
  exact h_main
