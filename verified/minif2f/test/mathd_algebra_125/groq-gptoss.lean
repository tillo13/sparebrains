import Mathlib

open scoped Nat
open scoped Real

/--
Today a father's age is five times his son's age. Exactly three years ago, the sum of their ages was 30. How old is the son today? -/
theorem mathd_algebra_125 (x y : ℕ) (h₀ : 0 < x ∧ 0 < y) (h₁ : 5 * x = y)
    (h₂ : ↑x - (3 : ℤ) + (y - (3 : ℤ)) = 30) : x = 6 := by
  -- From the sum three years ago we get the total sum today
  have h2' : (x : ℤ) + (y : ℤ) = 36 := by
    have := h₂
    linarith
  -- Cast the relation between ages to ℤ
  have hy : (y : ℤ) = 5 * (x : ℤ) := by
    have : (y : ℤ) = (5 * x : ℤ) := by
      exact_mod_cast h₁.symm
    simpa [Nat.cast_mul] using this
  -- Solve for the son's age in ℤ
  have hx : (x : ℤ) = 6 := by
    have : (x : ℤ) + 5 * (x : ℤ) = 36 := by
      simpa [hy] using h2'
    linarith
  -- Cast back to ℕ
  exact_mod_cast hx
