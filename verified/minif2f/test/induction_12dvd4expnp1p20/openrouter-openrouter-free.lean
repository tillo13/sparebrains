import Mathlib

open scoped Nat
open scoped Real

theorem induction_12dvd4expnp1p20 (n : ℕ) : 12 ∣ 4 ^ (n + 1) + 20 := by
  have h_pow_mod : ∀ n : ℕ, 4 ^ (n + 1) % 12 = 4 := by
    intro n
    have h : ∀ n : ℕ, 4 ^ (n + 1) % 12 = 4 := by
      intro n
      induction n with
      | zero =>
        norm_num
      | succ n ih =>
        rw [pow_succ, Nat.mul_mod, ih]
        <;> norm_num <;> omega
    exact h n
  
  have h_main : (4 ^ (n + 1) + 20) % 12 = 0 := by
    have h₁ : 4 ^ (n + 1) % 12 = 4 := h_pow_mod n
    have h₂ : (4 ^ (n + 1) + 20) % 12 = 0 := by
      have h₃ : (4 ^ (n + 1) + 20) % 12 = (4 ^ (n + 1) % 12 + 20 % 12) % 12 := by
        simp [Nat.add_mod]
      rw [h₃]
      have h₄ : 4 ^ (n + 1) % 12 = 4 := h₁
      rw [h₄]
      <;> norm_num
    exact h₂
  
  have h_final : 12 ∣ 4 ^ (n + 1) + 20 := by
    have h₁ : (4 ^ (n + 1) + 20) % 12 = 0 := h_main
    omega
  
  exact h_final
