import Mathlib

open scoped Nat
open scoped Real

/-- Find $n$ if $\gcd(n,40) = 10$ and $\mathop{\text{lcm}}[n,40] = 280$. -/
theorem mathd_numbertheory_100 (n : ℕ) (h₀ : 0 < n) (h₁ : Nat.gcd n 40 = 10)
    (h₂ : Nat.lcm n 40 = 280) : n = 70 := by
  have h3 : Nat.gcd n 40 * Nat.lcm n 40 = n * 40 := Nat.gcd_mul_lcm n 40
  rw [h₁, h₂] at h3
  -- h3 : 10 * 280 = n * 40
  have h4 : n * 40 = 70 * 40 := by
    calc
      n * 40 = 10 * 280 := by symm; exact h3
      _ = 2800 := by norm_num
      _ = 70 * 40 := by norm_num
  exact Nat.mul_right_cancel (by norm_num : 0 < 40) h4
