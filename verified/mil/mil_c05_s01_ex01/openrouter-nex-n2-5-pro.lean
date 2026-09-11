import Mathlib

/-- Mathematics in Lean, Chapter 5 §1 (Irrational Roots), exercise 1. Avigad & Massot, Apache-2.0, commit dd6d752. -/
theorem mil_c05_s01_ex01 {m : ℕ} (h : 2 ∣ m ^ 2) : 2 ∣ m := by
  have hmod : m % 2 = 0 := by
    have h2 : (m ^ 2) % 2 = 0 := Nat.mod_eq_zero_of_dvd h
    have hm : m % 2 = 0 ∨ m % 2 = 1 := Nat.mod_two_eq_zero_or_one m
    cases hm with
    | inl h0 => exact h0
    | inr h1 =>
        have : (m ^ 2) % 2 = 1 := by
          rw [pow_two]
          simp [h1, Nat.mul_mod]
        omega
  exact Nat.dvd_of_mod_eq_zero hmod
