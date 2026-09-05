import Mathlib

open scoped Nat
open scoped Real

/--
In an arithmetic sequence, the 7th term is 30, and the 11th term is 60. What is the 21st term of this sequence? -/
theorem mathd_algebra_354 (a d : ℝ) (h₀ : a + 6 * d = 30) (h₁ : a + 10 * d = 60) :
    a + 20 * d = 135 := by
  -- Express a + 20*d as a linear combination of (a + 6*d) and (a + 10*d)
  -- We need: α*(a + 6*d) + β*(a + 10*d) = a + 20*d
  -- This means: α + β = 1 and 6α + 10β = 20
  -- Solving: β = 7/2, α = -5/2
  -- So a + 20*d = (-5/2)*(a + 6*d) + (7/2)*(a + 10*d)
  -- = (-5/2)*30 + (7/2)*60 = -75 + 210 = 135
  have h_lin : a + 20 * d = (-(5:ℝ) / 2) * (a + 6 * d) + (7 / 2) * (a + 10 * d) := by
    -- Expand the right side
    -- (-5/2)*(a + 6d) + (7/2)*(a + 10d)
    -- = (-5/2)*a + (-5/2)*6d + (7/2)*a + (7/2)*10d
    -- = (-5/2 + 7/2)*a + (-30/2 + 70/2)*d
    -- = (2/2)*a + (40/2)*d
    -- = a + 20*d
    ring
  rw [h_lin, h₀, h₁]
  -- (-5/2)*30 + (7/2)*60
  -- = -75 + 210
  -- = 135
  norm_num
