import Mathlib

open scoped Nat
open scoped Real

/-- If $3a+2b=5$ and $a+b=2$, what is the ordered pair $(a,b)$ that satisfies both equations? -/
theorem mathd_algebra_513 (a b : ℝ) (h₀ : 3 * a + 2 * b = 5) (h₁ : a + b = 2) : a = 1 ∧ b = 1 := by
  have h₂ : 3 * (a + b) = 3 * 2 := by linarith
  have h₃ : 3 * a + 3 * b = 6 := by linarith
  have h₄ : (3 * a + 3 * b) - (3 * a + 2 * b) = 6 - 5 := by linarith
  have h₅ : b = 1 := by linarith
  have h₆ : a = 1 := by linarith
  exact ⟨h₆, h₅⟩
