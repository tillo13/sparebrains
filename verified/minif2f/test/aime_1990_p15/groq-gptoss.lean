import Mathlib

open scoped Nat
open scoped Real

/-- Find $ax^5 + by^5$ if the real numbers $a$, $b$, $x$, and $y$ satisfy the equations
\begin{eqnarray*} ax + by &=& 3, \\ ax^2 + by^2 &=& 7, \\ ax^3 + by^3 &=& 16, \\ ax^4 + by^4 &=& 42. \end{eqnarray*} -/
theorem aime_1990_p15 (a b x y : ℝ) (h₀ : a * x + b * y = 3) (h₁ : a * x ^ 2 + b * y ^ 2 = 7)
    (h₂ : a * x ^ 3 + b * y ^ 3 = 16) (h₃ : a * x ^ 4 + b * y ^ 4 = 42) :
    a * x ^ 5 + b * y ^ 5 = 20 := by
  -- recurrence identities
  have h_eq2 :
      (x + y) * (a * x ^ 2 + b * y ^ 2) - (x * y) * (a * x + b * y) =
        a * x ^ 3 + b * y ^ 3 := by
    ring
  have h_eq3 :
      (x + y) * (a * x ^ 3 + b * y ^ 3) - (x * y) * (a * x ^ 2 + b * y ^ 2) =
        a * x ^ 4 + b * y ^ 4 := by
    ring
  have h_eq5 :
      a * x ^ 5 + b * y ^ 5 =
        (x + y) * (a * x ^ 4 + b * y ^ 4) - (x * y) * (a * x ^ 3 + b * y ^ 3) := by
    ring
  -- substitute the given values
  have h1' : (x + y) * 7 - (x * y) * 3 = 16 := by
    have := h_eq2
    simpa [h₁, h₀, h₂] using this
  have h2' : (x + y) * 16 - (x * y) * 7 = 42 := by
    have := h_eq3
    simpa [h₂, h₁, h₃] using this
  -- solve for x + y and x * y
  have hxyp : x + y = -14 := by
    linarith [h1', h2']
  have hxy_mul : x * y = -38 := by
    linarith [h1', h2']
  -- compute the desired expression
  calc
    a * x ^ 5 + b * y ^ 5
        = (x + y) * (a * x ^ 4 + b * y ^ 4) - (x * y) * (a * x ^ 3 + b * y ^ 3) := by
          simpa using h_eq5
    _ = (x + y) * 42 - (x * y) * 16 := by
          simpa [h₃, h₂]
    _ = (-14) * 42 - (-38) * 16 := by
          simpa [hxyp, hxy_mul]
    _ = 20 := by
          ring
