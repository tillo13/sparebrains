import Mathlib

open scoped Nat
open scoped Real

theorem induction_11div10tonmn1ton (n : ℕ) : 11 ∣ 10 ^ n - (-1 : ℤ) ^ n := by
  -- first show 10 ≡ -1 [ZMOD 11]
  have h10 : (10 : ℤ) ≡ (-1 : ℤ) [ZMOD 11] := by
    -- need 11 ∣ (-1) - 10
    have hdiv : (11 : ℤ) ∣ ((-1 : ℤ) - 10) := by
      have h_eq : ((-1 : ℤ) - 10) = -11 := by ring
      have : (11 : ℤ) ∣ -11 := by
        exact dvd_neg.mpr (dvd_refl (11 : ℤ))
      simpa [h_eq] using this
    exact (Int.modEq_iff_dvd).mpr hdiv
  -- raise to power n
  have hpow := (h10.pow n)
  -- get divisibility from congruence
  have hdiv_pow : (11 : ℤ) ∣ ((-1 : ℤ) ^ n) - (10 : ℤ) ^ n :=
    (Int.modEq_iff_dvd).mp hpow
  -- flip sign
  have : (11 : ℤ) ∣ -((( -1 : ℤ) ^ n) - (10 : ℤ) ^ n) := by
    exact dvd_neg.mpr hdiv_pow
  simpa [neg_sub] using this
