import Mathlib

open scoped Nat
open scoped Real

/-- If

\begin{align*}
3x+4y-12z&=10,\\
-2x-3y+9z&=-4,
\end{align*}

compute $x$. -/
theorem mathd_algebra_388 (x y z : ℝ) (h₀ : 3 * x + 4 * y - 12 * z = 10)
    (h₁ : -2 * x - 3 * y + 9 * z = -4) : x = 14 := by
  have h₂ : 9 * x + 12 * y - 36 * z = 30 := by
    have h₂₁ : 9 * x + 12 * y - 36 * z = 3 * (3 * x + 4 * y - 12 * z) := by
      ring
    rw [h₂₁]
    rw [h₀]
    <;> norm_num
  
  have h₃ : -8 * x - 12 * y + 36 * z = -16 := by
    have h₃₁ : -8 * x - 12 * y + 36 * z = 4 * (-2 * x - 3 * y + 9 * z) := by
      ring
    rw [h₃₁]
    rw [h₁]
    <;> norm_num
  
  have h₄ : x = 14 := by
    have h₄₁ : (9 * x + 12 * y - 36 * z) + (-8 * x - 12 * y + 36 * z) = 30 + (-16) := by
      linarith
    -- Simplify the left side of the equation
    have h₄₂ : (9 * x + 12 * y - 36 * z) + (-8 * x - 12 * y + 36 * z) = x := by
      ring
    -- Simplify the right side of the equation
    have h₄₃ : (30 : ℝ) + (-16 : ℝ) = 14 := by norm_num
    -- Combine the simplified equations to get x = 14
    linarith
  
  exact h₄
