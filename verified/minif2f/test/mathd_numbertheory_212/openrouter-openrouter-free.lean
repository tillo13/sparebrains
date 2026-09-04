import Mathlib

open scoped Nat
open scoped Real

/-- Find the units digit of $16^{17} \times 17^{18} \times 18^{19}$. -/
theorem mathd_numbertheory_212 : 16 ^ 17 * 17 ^ 18 * 18 ^ 19 % 10 = 8 := by
  have h_main : 16 ^ 17 * 17 ^ 18 * 18 ^ 19 % 10 = 8 := by
    norm_num [pow_succ, Nat.mul_mod, Nat.pow_mod, Nat.mod_mod]
    <;> rfl
  
  rw [h_main]
  <;> norm_num
