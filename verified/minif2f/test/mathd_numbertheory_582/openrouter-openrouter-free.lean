import Mathlib

open scoped Nat
open scoped Real

/--
If $n$ is a multiple of three, what is the remainder when $(n + 4) + (n + 6) + (n + 8)$ is divided by $9$? -/
theorem mathd_numbertheory_582 (n : ℕ) (h₀ : 0 < n) (h₁ : 3 ∣ n) :
    (n + 4 + (n + 6) + (n + 8)) % 9 = 0 := by
  have h : n + 4 + (n + 6) + (n + 8) = 3 * n + 18 := by ring
  rw [h]
  cases' h₁ with k hk
  rw [hk]
  have h2 : 3 * (3 * k) + 18 = 9 * (k + 2) := by ring
  rw [h2]
  exact Nat.mod_eq_zero_of_dvd (Nat.dvd_mul_right _ _)
