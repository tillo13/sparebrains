import Mathlib

open scoped Nat
open scoped Real

/--
In an arithmetic sequence, the 7th term is 30, and the 11th term is 60. What is the 21st term of this sequence? -/
theorem mathd_algebra_354 (a d : ℝ) (h₀ : a + 6 * d = 30) (h₁ : a + 10 * d = 60) :
    a + 20 * d = 135 := by
  have h2 : 4 * d = 30 := by linarith [h₀, h₁]
  calc a + 20 * d = a + 6 * d + 14 * d := by ring
    _ = 30 + 14 * d := by rw [h₀]
    _ = 30 + (7/2) * (4 * d) := by ring
    _ = 30 + (7/2) * 30 := by rw [h2]
    _ = 30 + 105 := by norm_num
    _ = 135 := by norm_num
