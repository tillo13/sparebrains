import Mathlib

open scoped Nat
open scoped Real

/-- Determine the remainder of 54 (mod 6). -/
theorem mathd_numbertheory_342 : 54 % 6 = 0 := by
  have h : 54 % 6 = 0 := by
    norm_num [Nat.mod_eq_of_lt]
    <;> rfl
  
  rw [h]
  <;> rfl
