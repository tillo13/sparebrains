import Mathlib

open scoped Nat
open scoped Real

/-- Find the units digit of $29 \cdot 79 + 31 \cdot 81$. -/
theorem mathd_numbertheory_235 : (29 * 79 + 31 * 81) % 10 = 2 := by
  have : 29 * 79 + 31 * 81 = 29 * 79 + 31 * 81 := by ring
  have : 29 * 79 = 2291 := by ring
  have : 31 * 81 = 2511 := by ring
  have : 2291 + 2511 = 4802 := by ring
  have : 4802 % 10 = 2 := by ring
  exact this
