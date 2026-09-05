import Mathlib

open scoped Nat
open scoped Real

/-- If $3a+2b=5$ and $a+b=2$, what is the ordered pair $(a,b)$ that satisfies both equations? -/
theorem mathd_algebra_513 (a b : ℝ) (h₀ : 3 * a + 2 * b = 5) (h₁ : a + b = 2) : a = 1 ∧ b = 1 := by
  have ha : a = 1 := by
    calc
      a = (3 * a + 2 * b) - 2 * (a + b) := by ring
      _ = 5 - 2 * 2 := by rw [h₀, h₁]
      _ = 1 := by norm_num
  have hb : b = 1 := by
    calc
      b = 3 * (a + b) - (3 * a + 2 * b) := by ring
      _ = 3 * 2 - 5 := by rw [h₁, h₀]
      _ = 1 := by norm_num
  constructor
  · exact ha
  · exact hb
