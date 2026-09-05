import Mathlib

open scoped Nat
open scoped Real

/-- Find the units digit of $16^{17} \times 17^{18} \times 18^{19}$. -/
theorem mathd_numbertheory_212 : 16 ^ 17 * 17 ^ 18 * 18 ^ 19 % 10 = 8 := by
  calc
    16 ^ 17 * 17 ^ 18 * 18 ^ 19 % 10
        = ((16 % 10) ^ 17 * (17 % 10) ^ 18 * (18 % 10) ^ 19) % 10 := by
          simp [Nat.mul_mod, Nat.pow_mod]
    _ = ((6 ^ 17) * (7 ^ 18) * (8 ^ 19)) % 10 := by
          simp
    _ = 8 := by
          norm_num
