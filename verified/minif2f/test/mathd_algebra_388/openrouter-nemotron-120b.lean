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
  have h2 : x = 14 := by
    have h3 : 3 * (3 * x + 4 * y - 12 * z) + 4 * (-2 * x - 3 * y + 9 * z) = x := by
      ring_nf
      <;> linarith
    have h4 : 3 * (3 * x + 4 * y - 12 * z) + 4 * (-2 * x - 3 * y + 9 * z) = 3 * 10 + 4 * (-4) := by
      linarith
    linarith
  exact h2
