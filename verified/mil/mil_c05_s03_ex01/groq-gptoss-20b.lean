import Mathlib

open BigOperators

/-- Mathematics in Lean, Chapter 5 §3 (Infinitely Many Primes), exercise 1. Avigad & Massot, Apache-2.0, commit dd6d752. -/
theorem mil_c05_s03_ex01 {m : ℕ} (h0 : m ≠ 0) (h1 : m ≠ 1) : 2 ≤ m := by
  have hlt : 1 < m := by
    have hpos : 0 < m := Nat.pos_of_ne_zero h0
    have hle : 1 ≤ m := Nat.succ_le_of_lt hpos
    exact lt_of_le_of_ne hle (ne_comm.mp h1)
  exact (Nat.succ_le_iff).mpr hlt
