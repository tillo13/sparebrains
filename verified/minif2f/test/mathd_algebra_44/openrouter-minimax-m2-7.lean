import Mathlib

open scoped Nat
open scoped Real

/--
At which point do the lines $s=9-2t$ and $t=3s+1$ intersect? Give your answer as an ordered pair in the form $(s, t).$ -/
theorem mathd_algebra_44 (s t : ℝ) (h₀ : s = 9 - 2 * t) (h₁ : t = 3 * s + 1) : s = 1 ∧ t = 4 := by
  rw [h₁] at h₀
  have h2 : s = 7 - 6 * s := calc
    s = 9 - 2 * (3 * s + 1) := h₀
    _ = 9 - 2 * (3 * s + 1) := by ring
    _ = 7 - 6 * s := by ring
  have hs : s = 1 := by linarith
  constructor
  · exact hs
  · calc t = 3 * s + 1 := h₁
      _ = 3 * 1 + 1 := by rw [hs]
      _ = 4 := by ring
