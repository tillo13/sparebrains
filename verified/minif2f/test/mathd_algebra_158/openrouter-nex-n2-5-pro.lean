import Mathlib

open scoped Nat
open scoped Real

/--
The sum of 5 consecutive even integers is 4 less than the sum of the first 8 consecutive odd counting numbers. What is the smallest of the even integers? -/
theorem mathd_algebra_158 (a : ℕ) (h₀ : Even a)
    (h₁ : ↑(∑ k ∈ Finset.range 8, (2 * k + 1)) - ↑(∑ k ∈ Finset.range 5, (a + 2 * k)) = (4 : ℤ)) :
    a = 8 := by
  have h₂ : (a : ℤ) = 8 := by
    norm_num [Finset.sum_range_succ, Nat.cast_add, Nat.cast_mul, Nat.cast_one, Nat.cast_zero] at h₁
    omega
  exact_mod_cast h₂
