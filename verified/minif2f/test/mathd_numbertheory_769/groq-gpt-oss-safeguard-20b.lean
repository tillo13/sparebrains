import Mathlib

open scoped Nat
open scoped Real

/-- What is the remainder when $129^{34}+96^{38}$ is divided by $11$? -/
theorem mathd_numbertheory_769 : (129 ^ 34 + 96 ^ 38) % 11 = 9 := by
  -- Split the sum modulo 11
  have h1 : (129 ^ 34 + 96 ^ 38) % 11 =
      ((129 ^ 34) % 11 + (96 ^ 38) % 11) % 11 := by
    simpa using Nat.add_mod (129 ^ 34) (96 ^ 38) 11
  -- Reduce the powers modulo 11
  have h2 : (129 ^ 34) % 11 = (129 % 11) ^ 34 % 11 := by
    simpa using Nat.pow_mod 129 34 11
  have h3 : (96 ^ 38) % 11 = (96 % 11) ^ 38 % 11 := by
    simpa using Nat.pow_mod 96 38 11
  -- Compute the small remainders
  have h4 : 129 % 11 = 8 := by norm_num
  have h5 : 96 % 11 = 8 := by norm_num
  have h6 : (8 ^ 34) % 11 = 4 := by norm_num
  have h7 : (8 ^ 38) % 11 = 5 := by norm_num
  calc
    (129 ^ 34 + 96 ^ 38) % 11
        = ((129 ^ 34) % 11 + (96 ^ 38) % 11) % 11 := h1
    _ = ((129 % 11) ^ 34 % 11 + (96 % 11) ^ 38 % 11) % 11 := by
          simp [h2, h3]
    _ = ((8) ^ 34 % 11 + (8) ^ 38 % 11) % 11 := by
          simp [h4, h5]
    _ = (4 + 5) % 11 := by
          simp [h6, h7]
    _ = 9 % 11 := by norm_num
    _ = 9 := by norm_num
