import Mathlib

open scoped Nat
open scoped Real

/--
At which point do the lines $s=9-2t$ and $t=3s+1$ intersect? Give your answer as an ordered pair in the form $(s, t).$ -/
theorem mathd_algebra_44 (s t : ℝ) (h₀ : s = 9 - 2 * t) (h₁ : t = 3 * s + 1) : s = 1 ∧ t = 4 := by
  have h₂ : s = 1 := by
    have h₂₁ : s = 9 - 2 * (3 * s + 1) := by
      rw [h₁] at h₀
      exact h₀
    have h₂₂ : s = 7 - 6 * s := by
      linarith
    have h₂₃ : 7 * s = 7 := by linarith
    have h₂₄ : s = 1 := by
      apply mul_left_cancel₀ (show (7 : ℝ) ≠ 0 by norm_num)
      linarith
    exact h₂₄
  
  have h₃ : t = 4 := by
    rw [h₁]
    rw [h₂]
    <;> norm_num
  
  have h₄ : s = 1 ∧ t = 4 := by
    exact ⟨h₂, h₃⟩
  
  exact h₄
