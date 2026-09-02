import Mathlib

open scoped Nat
open scoped Real

/--
The sum of 5 consecutive even integers is 4 less than the sum of the first 8 consecutive odd counting numbers. What is the smallest of the even integers? -/
theorem mathd_algebra_158 (a : ℕ) (h₀ : Even a)
    (h₁ : ↑(∑ k ∈ Finset.range 8, (2 * k + 1)) - ↑(∑ k ∈ Finset.range 5, (a + 2 * k)) = (4 : ℤ)) :
    a = 8 := by
  have hsum_odds : (∑ k ∈ Finset.range 8, (2 * k + 1) : ℕ) = 64 := by
    decide
  have hsum_evens : (∑ k ∈ Finset.range 5, (a + 2 * k) : ℕ) = 5 * a + 20 := by
    simp [Finset.sum_range_succ, add_assoc, add_comm, add_left_comm]
    ring
  have hsum_odds_int : ↑(∑ k ∈ Finset.range 8, (2 * k + 1) : ℕ) = (64 : ℤ) := by
    rw [hsum_odds]
    simp
  have hsum_evens_int : ↑(∑ k ∈ Finset.range 5, (a + 2 * k) : ℕ) = (5 * a + 20 : ℤ) := by
    rw [hsum_evens]
    simp
  rw [hsum_odds_int, hsum_evens_int] at h₁
  omega
