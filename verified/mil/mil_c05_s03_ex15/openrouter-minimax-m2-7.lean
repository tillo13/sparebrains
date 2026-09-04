import Mathlib

open BigOperators
open Finset

/-- Mathematics in Lean, Chapter 5 §3 (Infinitely Many Primes), exercise 15. Avigad & Massot, Apache-2.0, commit dd6d752. -/
theorem mil_c05_s03_ex15 {m n : ℕ} (h₀ : m ∣ n) (h₁ : 2 ≤ m) (h₂ : m < n) : n / m ∣ n ∧ n / m < n := by
  have hm : m > 0 := Nat.zero_lt_of_lt h₁
  have hn : n > 0 := Nat.lt_trans hm h₂
  have h₁' : 1 < m := Nat.lt_of_succ_le h₁
  have eq := Nat.div_mul_cancel h₀
  have := Nat.div_lt_self hn h₁'
  constructor
  · use m
    rw [eq]
  · exact this
