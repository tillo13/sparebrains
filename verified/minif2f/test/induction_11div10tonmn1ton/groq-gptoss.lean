import Mathlib

open scoped Nat
open scoped Real

theorem induction_11div10tonmn1ton (n : ℕ) : 11 ∣ 10 ^ n - (-1 : ℤ) ^ n := by
  -- First show 10 ≡ -1 [ZMOD 11]
  have h10 : (10 : ℤ) ≡ (-1 : ℤ) [ZMOD (11 : ℤ)] := by
    have : (11 : ℤ) ∣ ((-1 : ℤ) - 10) := by
      norm_num
    exact (Int.modEq_iff_dvd).mpr this
  -- Raise to the n-th power
  have hpow := h10.pow n
  -- From the modular equivalence we obtain a divisibility statement
  have hdiv : (11 : ℤ) ∣ ((-1 : ℤ) ^ n) - (10 : ℤ) ^ n := hpow.dvd
  -- Flip the sign to get the desired form
  simpa [neg_sub] using (dvd_neg.mpr hdiv)
