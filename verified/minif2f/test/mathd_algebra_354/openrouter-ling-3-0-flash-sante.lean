import Mathlib

open scoped Nat
open scoped Real

/--
In an arithmetic sequence, the 7th term is 30, and the 11th term is 60. What is the 21st term of this sequence? -/
theorem mathd_algebra_354 (a d : ℝ) (h₀ : a + 6 * d = 30) (h₁ : a + 10 * d = 60) :
    a + 20 * d = 135 := by
  have h₂ : 4 * d = 30 := by linarith [h₀, h₁]
  have h₃ : d = 15/2 := by linarith [h₂]
  rw [h₃] at h₀
  rw [h₃] at ⊢
  -- now a + 6*(15/2) = 30, i.e., a + 45 = 30, so a = -15
  -- goal: a + 20*(15/2) = 135, i.e., a + 150 = 135
  have h₄ : a = -15 := by linarith [h₀]
  rw [h₄]
  norm_num
