import Mathlib

open scoped Nat
open scoped Real

/--
Because of redistricting, Liberty Middle School's enrollment increased to 598 students. This is an increase of $4\%$ over last year's enrollment. What was last year's enrollment? -/
theorem mathd_algebra_137 (x : ℕ) (h₀ : ↑x + (4 : ℝ) / (100 : ℝ) * ↑x = 598) : x = 575 := by
  have h₁ : (1 : ℝ) + (4 / 100 : ℝ) = (104 / 100 : ℝ) := by ring
  have h₂ : ((1 : ℝ) + (4 / 100 : ℝ)) * (↑x : ℝ) = 598 := by
    linarith [h₀]
  rw [h₁] at h₂
  have h₃ : (↑x : ℝ) = 598 * (100 / 104 : ℝ) := by
    linarith
  have h₄ : (598 : ℝ) * (100 / 104 : ℝ) = 575 := by norm_num
  rw [h₄] at h₃
  have h₅ : (575 : ℝ) = 575 := by norm_num
  have h₆ : (x : ℕ) = (575 : ℕ) := by
    have hx : (↑x : ℝ) = (575 : ℝ) := by linarith
    have hx' : (x : ℝ) = (575 : ℝ) := hx
    exact_mod_cast hx'
  exact h₆
