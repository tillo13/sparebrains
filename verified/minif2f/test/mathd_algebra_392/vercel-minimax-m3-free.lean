import Mathlib

open scoped Nat
open scoped Real

/--
The sum of the squares of three consecutive positive even numbers is $12296$. Find the product of the three numbers divided by $8$. -/
theorem mathd_algebra_392 (n : ℕ) (h₀ : Even n)
    (h₁ : (↑n - 2) ^ 2 + ↑n ^ 2 + (↑n + 2) ^ 2 = (12296 : ℤ)) :
    (↑n - 2) * ↑n * (↑n + 2) / 8 = (32736 : ℤ) := by
  have h_eq : (n : ℤ) = 64 := by
    have h₁' := h₁
    nlinarith [h₁', h₀, Int.ofNat_zero_le n, show (n : ℤ) ≥ 0 by positivity, sq_nonneg ((n : ℤ) - 64)]
  rw [h_eq]
  norm_num
