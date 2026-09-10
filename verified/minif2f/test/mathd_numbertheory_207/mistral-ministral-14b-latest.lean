import Mathlib

open scoped Nat
open scoped Real

/-- Convert $852_9$ to base 10. -/
theorem mathd_numbertheory_207 : 8 * 9 ^ 2 + 5 * 9 + 2 = 695 := by
  have h1 : 9 ^ 2 = 81 := by ring
  have h2 : 8 * 81 = 648 := by ring
  have h3 : 5 * 9 = 45 := by ring
  have h4 : 648 + 45 = 693 := by ring
  have h5 : 693 + 2 = 695 := by ring
  rw [h1, h2, h3, h4, h5]
