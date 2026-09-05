import Mathlib

open scoped Nat
open scoped Real

/--
My father's age is $1222_{3}$, in base three to represent his three lower limbs -- two legs and a cane.  How old is he in base ten? -/
theorem mathd_numbertheory_85 : 1 * 3 ^ 3 + 2 * 3 ^ 2 + 2 * 3 + 2 = 53 := by
  simp [pow_succ, mul_add, mul_comm, mul_assoc, add_assoc, add_comm]
