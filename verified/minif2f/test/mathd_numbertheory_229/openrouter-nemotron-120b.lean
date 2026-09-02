import Mathlib

open scoped Nat
open scoped Real

/-- What is the remainder when $5^{30}$ is divided by 7? -/
theorem mathd_numbertheory_229 : 5 ^ 30 % 7 = 1 := by
  have h : 5 ^ 6 % 7 = 1 := by norm_num
  have h₂ : 5 ^ 30 % 7 = 1 := by
    have h3 : 5 ^ 30 = (5 ^ 6) ^ 5 := by
      rw [← pow_mul]
      <;> norm_num
    rw [h3]
    have h4 : ((5 ^ 6) ^ 5) % 7 = (((5 ^ 6) % 7) ^ 5) % 7 := by
      rw [← Nat.pow_mod]
    rw [h4]
    rw [h]
    norm_num
  exact h₂
