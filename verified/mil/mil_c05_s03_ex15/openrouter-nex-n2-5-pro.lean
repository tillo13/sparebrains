import Mathlib

open BigOperators
open Finset

/-- Mathematics in Lean, Chapter 5 §3 (Infinitely Many Primes), exercise 15. Avigad & Massot, Apache-2.0, commit dd6d752. -/
theorem mil_c05_s03_ex15 {m n : ℕ} (h₀ : m ∣ n) (h₁ : 2 ≤ m) (h₂ : m < n) : n / m ∣ n ∧ n / m < n := by
  have hm : 0 < m := by linarith
  have hn : 0 < n := by linarith
  have hmn : n = m * (n / m) := by
    rw [Nat.mul_div_cancel' h₀]
  constructor
  · exact ⟨m, by linarith⟩
  · exact Nat.div_lt_self hn (by linarith)
