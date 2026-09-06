import Mathlib

open BigOperators

/-- Mathematics in Lean, Chapter 5 §3 (Infinitely Many Primes), exercise 1. Avigad & Massot, Apache-2.0, commit dd6d752. -/
theorem mil_c05_s03_ex01 {m : ℕ} (h0 : m ≠ 0) (h1 : m ≠ 1) : 2 ≤ m := by
  -- First, show that `1 ≤ m`.
  have h1le : 1 ≤ m := by
    have hpos : 0 < m := Nat.pos_of_ne_zero h0
    exact Nat.succ_le_of_lt hpos
  -- Then, deduce that `1 < m`.
  have h1lt : 1 < m := lt_of_le_of_ne h1le (by
    -- `1 ≠ m` follows from `m ≠ 1`.
    exact h1.symm)
  -- Finally, convert `1 < m` to `2 ≤ m`.
  exact (Nat.succ_le_iff).mpr h1lt
