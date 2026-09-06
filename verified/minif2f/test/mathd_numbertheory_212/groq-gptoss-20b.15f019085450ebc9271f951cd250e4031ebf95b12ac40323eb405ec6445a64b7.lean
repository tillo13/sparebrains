import Mathlib

open scoped Nat
open scoped Real

/-- Find the units digit of $16^{17} \times 17^{18} \times 18^{19}$. -/
theorem mathd_numbertheory_212 : 16 ^ 17 * 17 ^ 18 * 18 ^ 19 % 10 = 8 := by
  have h16 : (16 ^ 17) % 10 = 6 := by
    have : (16 % 10) ^ 17 % 10 = 6 := by norm_num
    simpa [Nat.pow_mod] using this
  have h17 : (17 ^ 18) % 10 = 9 := by
    have : (17 % 10) ^ 18 % 10 = 9 := by norm_num
    simpa [Nat.pow_mod] using this
  have h18 : (18 ^ 19) % 10 = 2 := by
    have : (18 % 10) ^ 19 % 10 = 2 := by norm_num
    simpa [Nat.pow_mod] using this
  calc
    16 ^ 17 * 17 ^ 18 * 18 ^ 19 % 10
        = ((16 ^ 17 * 17 ^ 18) % 10 * (18 ^ 19 % 10)) % 10 := by
          simpa [Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc] using
            (Nat.mul_mod (16 ^ 17 * 17 ^ 18) (18 ^ 19) 10)
    _ = (((16 ^ 17 % 10) * (17 ^ 18 % 10)) % 10 * (18 ^ 19 % 10)) % 10 := by
          simpa using (Nat.mul_mod (16 ^ 17) (17 ^ 18) 10)
    _ = (((6) * (9)) % 10 * (2)) % 10 := by
          simp [h16, h17, h18]
    _ = ((54 % 10) * 2) % 10 := by
          norm_num
    _ = ((4) * 2) % 10 := by
          norm_num
    _ = 8 % 10 := by
          norm_num
    _ = 8 := by
          norm_num
