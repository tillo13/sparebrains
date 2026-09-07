import Mathlib

open scoped Nat
open scoped Real

/-- Determine the remainder of 194 (mod 11). -/
theorem mathd_numbertheory_66 : 194 % 11 = 7 := by
  have : 194 = 11 * 17 + 7 := by
    ring
  rw [this]
