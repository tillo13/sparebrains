import Mathlib

open scoped Nat
open scoped Real

/--
In an arithmetic sequence, the 7th term is 30, and the 11th term is 60. What is the 21st term of this sequence? -/
theorem mathd_algebra_354 (a d : ℝ) (h₀ : a + 6 * d = 30) (h₁ : a + 10 * d = 60) :
    a + 20 * d = 135 := by
  have h₂ : 4 * d = 30 := by
    have h₂₁ : (a + 10 * d) - (a + 6 * d) = 60 - 30 := by
      rw [h₁, h₀]
      <;> norm_num
    -- Simplify the left side to get 4 * d = 30
    have h₂₂ : 4 * d = 30 := by
      linarith
    exact h₂₂
  
  have h₃ : 10 * d = 75 := by
    have h₃₁ : 10 * d = 75 := by
      -- We know that 4 * d = 30, so we can multiply both sides by 2.5 to get 10 * d = 75.
      -- Alternatively, we can solve for d and then multiply by 10.
      have h₃₂ : d = 30 / 4 := by
        -- Solve for d from 4 * d = 30
        have h₃₃ : 4 * d = 30 := h₂
        linarith
      -- Substitute d = 30 / 4 into 10 * d
      rw [h₃₂]
      <;> norm_num
    exact h₃₁
  
  have h₄ : a + 20 * d = 135 := by
    have h₄₁ : a + 20 * d = 135 := by
      -- We know that a + 10 * d = 60 and 10 * d = 75.
      -- We can add these two equations to get a + 20 * d = 135.
      have h₄₂ : a + 10 * d = 60 := h₁
      have h₄₃ : 10 * d = 75 := h₃
      -- Add the two equations: (a + 10 * d) + 10 * d = 60 + 75
      have h₄₄ : a + 20 * d = 135 := by
        linarith
      exact h₄₄
    exact h₄₁
  
  rw [h₄]
  <;> norm_num
