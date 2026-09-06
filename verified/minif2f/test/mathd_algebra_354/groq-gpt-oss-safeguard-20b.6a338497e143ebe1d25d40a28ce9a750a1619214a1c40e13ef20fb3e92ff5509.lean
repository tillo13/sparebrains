import Mathlib

open scoped Nat
open scoped Real

/--
In an arithmetic sequence, the 7th term is 30, and the 11th term is 60. What is the 21st term of this sequence? -/
theorem mathd_algebra_354 (a d : ℝ) (h₀ : a + 6 * d = 30) (h₁ : a + 10 * d = 60) :
    a + 20 * d = 135 := by
  -- From the two equations we can deduce the common difference
  have h₂ : 4 * d = 30 := by
    linarith
  -- Express `a` in terms of `d`
  have h₃ : a = 30 - 6 * d := by
    linarith
  -- Solve for `d`
  have h₄ : d = 30 / 4 := by
    have h₄' : (4 : ℝ) ≠ 0 := by norm_num
    have : d * 4 = 30 := by
      simpa [mul_comm] using h₂
    exact (eq_div_iff_mul_eq h₄').2 this
  -- Compute the 21st term
  calc
    a + 20 * d = (30 - 6 * d) + 20 * d := by simpa [h₃]
    _ = 30 + 14 * d := by ring
    _ = 30 + 14 * (30 / 4) := by simpa [h₄]
    _ = 135 := by norm_num
