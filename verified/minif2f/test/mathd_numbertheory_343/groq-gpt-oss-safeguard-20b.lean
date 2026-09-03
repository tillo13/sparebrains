import Mathlib

open scoped Nat
open scoped Real

/-- What is the units digit of the product of all of the odd integers between 0 and 12? -/
theorem mathd_numbertheory_343 : (∏ k ∈ Finset.range 6, (2 * k + 1)) % 10 = 5 := by
  have hprod : (∏ k ∈ Finset.range 6, (2 * k + 1)) = 10395 := by
    norm_num
  simpa [hprod] using (by norm_num : 10395 % 10 = 5)
