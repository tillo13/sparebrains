import Mathlib

open scoped Nat
open scoped Real

/--
In an arithmetic sequence, the 7th term is 30, and the 11th term is 60. What is the 21st term of this sequence? -/
theorem mathd_algebra_354 (a d : ℝ) (h₀ : a + 6 * d = 30) (h₁ : a + 10 * d = 60) :
    a + 20 * d = 135 := by
  calc a + 20 * d = (-5/2) * (a + 6 * d) + (7/2) * (a + 10 * d) := by ring
               _ = (-5/2) * 30 + (7/2) * 60 := by rw [h₀, h₁]
               _ = 135 := by ring
