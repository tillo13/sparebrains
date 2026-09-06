import Mathlib

open scoped Nat
open scoped Real

/-- Given $f(x)=cx^3-9x+3$ and $f(2)=9$, find the value of $c$. -/
theorem mathd_algebra_148 (c : ℝ) (f : ℝ → ℝ) (h₀ : ∀ x, f x = c * x ^ 3 - 9 * x + 3)
    (h₁ : f 2 = 9) : c = 3 := by
  have h₂ : f 2 = c * 2 ^ 3 - 9 * 2 + 3 := h₀ 2
  rw [h₁] at h₂
  -- h₂ : 9 = c * 8 - 18 + 3
  -- Simplify: 9 = 8c - 15
  have h₃ : 9 = c * 8 - 15 := by
    rw [h₂]
    ring
  -- 8c = 24
  have h₄ : c * 8 = 24 := by
    linarith [h₃]
  -- c = 3
  have h₅ : c = 3 := by
    linarith [h₄]
  exact h₅
