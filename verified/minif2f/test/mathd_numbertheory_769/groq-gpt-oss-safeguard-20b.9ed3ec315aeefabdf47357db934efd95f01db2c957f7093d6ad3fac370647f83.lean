import Mathlib

open scoped Nat
open scoped Real

/-- What is the remainder when $129^{34}+96^{38}$ is divided by $11$? -/
theorem mathd_numbertheory_769 : (129 ^ 34 + 96 ^ 38) % 11 = 9 := by
  have h129 : 129 % 11 = 8 := by norm_num
  have h96 : 96 % 11 = 8 := by norm_num
  have hpow34 : (129 ^ 34) % 11 = 8 ^ 34 % 11 := by
    simpa [h129] using Nat.pow_mod 129 34 11
  have hpow38 : (96 ^ 38) % 11 = 8 ^ 38 % 11 := by
    simpa [h96] using Nat.pow_mod 96 38 11
  have hpow34mod : 8 ^ 34 % 11 = 4 := by
    -- compute using pow_mod cycle
    -- we can use `norm_num` again
    norm_num
  have hpow38mod : 8 ^ 38 % 11 = 5 := by
    norm_num
  calc
    (129 ^ 34 + 96 ^ 38) % 11
        = ((129 ^ 34) % 11 + (96 ^ 38) % 11) % 11 := by
          simpa [Nat.add_mod] using rfl
    _ = (8 ^ 34 % 11 + 8 ^ 38 % 11) % 11 := by
          simp [hpow34, hpow38]
    _ = (4 + 5) % 11 := by
          simp [hpow34mod, hpow38mod]
    _ = 9 % 11 := by norm_num
    _ = 9 := by norm_num
