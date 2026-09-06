import Mathlib

open scoped Nat
open scoped Real

/-- Consider the function $f(x)=5x+4$.  What is $f(1)$? -/
theorem mathd_algebra_171 (f : ℝ → ℝ) (h₀ : ∀ x, f x = 5 * x + 4) : f 1 = 9 := by
  have h₁ : f 1 = 5 * (1 : ℝ) + 4 := by
    have h₂ : f 1 = 5 * (1 : ℝ) + 4 := by
      -- Apply the given hypothesis to x = 1
      have h₃ := h₀ 1
      -- Simplify the expression using the hypothesis
      norm_num at h₃ ⊢
      <;> linarith
    -- The result follows directly from the hypothesis
    exact h₂
  
  have h₂ : f 1 = 9 := by
    -- Simplify the right-hand side of h₁ to get 9
    norm_num at h₁ ⊢
    <;> linarith
  
  -- The final result follows directly from h₂
  exact h₂
