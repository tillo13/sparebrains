import Mathlib

open scoped Nat
open scoped Real

/-- Determine the remainder of 194 (mod 11). -/
theorem mathd_numbertheory_66 : 194 % 11 = 7 := by
  have h_main : 194 % 11 = 7 := by
    norm_num [Nat.mod_eq_of_lt]
    <;> rfl
  
  rw [h_main]
  <;> rfl
