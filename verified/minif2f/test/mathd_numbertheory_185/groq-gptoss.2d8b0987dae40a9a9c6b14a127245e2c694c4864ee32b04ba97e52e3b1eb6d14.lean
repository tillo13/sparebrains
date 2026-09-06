import Mathlib

open scoped Nat
open scoped Real

/--
When a number is divided by 5, the remainder is 3. What is the remainder when twice the number is divided by 5? -/
theorem mathd_numbertheory_185 (n : ℕ) (h₀ : n % 5 = 3) : 2 * n % 5 = 1 := by
  have hmod : (n % 5) * 2 % 5 = n * 2 % 5 := by
    simpa using (Nat.mod_mul_left_mod n 2 5)
  calc
    2 * n % 5 = n * 2 % 5 := by
      simpa [Nat.mul_comm]
    _ = (n % 5) * 2 % 5 := by
      symm
      exact hmod
    _ = 3 * 2 % 5 := by
      simpa [h₀]
    _ = 6 % 5 := by rfl
    _ = 1 := by
      norm_num
