import Mathlib

open scoped Nat
open scoped Real

/--
Today a father's age is five times his son's age. Exactly three years ago, the sum of their ages was 30. How old is the son today? -/
theorem mathd_algebra_125 (x y : ℕ) (h₀ : 0 < x ∧ 0 < y) (h₁ : 5 * x = y)
    (h₂ : ↑x - (3 : ℤ) + (y - (3 : ℤ)) = 30) : x = 6 := by
  -- sum of ages three years ago gives a total of 30
  have hsum : (x : ℤ) + (y : ℤ) = 36 := by
    have h := h₂
    have : (x : ℤ) - 3 + (y - 3) = 30 := by
      simpa using h
    have : (x : ℤ) + (y : ℤ) - 6 = 30 := by
      simpa [sub_eq_add_neg, add_comm, add_left_comm, add_assoc] using this
    linarith
  -- father's age is five times the son's age
  have hy : (y : ℤ) = 5 * (x : ℤ) := by
    have := congrArg (fun n : ℕ => (n : ℤ)) h₁
    simpa [Nat.cast_mul] using this.symm
  -- solve for the son's age
  have hx_int : (x : ℤ) = 6 := by
    have : (x : ℤ) + 5 * (x : ℤ) = 36 := by
      simpa [hy] using hsum
    linarith
  exact_mod_cast hx_int
