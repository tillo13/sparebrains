import Mathlib

open scoped Nat
open scoped Real

/-- Find $n$ if $\gcd(n,40) = 10$ and $\mathop{\text{lcm}}[n,40] = 280$. -/
theorem mathd_numbertheory_100 (n : ℕ) (h₀ : 0 < n) (h₁ : Nat.gcd n 40 = 10)
    (h₂ : Nat.lcm n 40 = 280) : n = 70 := by
  have h₃ : Nat.gcd n 40 * Nat.lcm n 40 = n * 40 := by
    have h₃₁ : Nat.gcd n 40 * Nat.lcm n 40 = n * 40 := by
      rw [Nat.gcd_mul_lcm n 40]
      <;> ring_nf
      <;> norm_num
    exact h₃₁
  
  have h₄ : 10 * 280 = n * 40 := by
    calc
      10 * 280 = Nat.gcd n 40 * Nat.lcm n 40 := by
        rw [h₁, h₂]
        <;> norm_num
      _ = n * 40 := by
        rw [h₃]
        <;> ring_nf
        <;> norm_num
  
  have h₅ : n * 40 = 70 * 40 := by
    have h₅₁ : n * 40 = 2800 := by
      have h₅₂ : 10 * 280 = n * 40 := h₄
      have h₅₃ : 10 * 280 = 2800 := by norm_num
      linarith
    have h₅₄ : 70 * 40 = 2800 := by norm_num
    linarith
  
  have h₆ : n = 70 := by
    have h₆₁ : n * 40 = 70 * 40 := h₅
    have h₆₂ : 0 < 40 := by norm_num
    have h₆₃ : n = 70 := by
      apply Nat.eq_of_mul_eq_mul_right h₆₂
      linarith
    exact h₆₃
  
  rw [h₆]
  <;> norm_num
