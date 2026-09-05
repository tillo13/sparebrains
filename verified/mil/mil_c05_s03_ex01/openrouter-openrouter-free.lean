import Mathlib

open BigOperators

/-- Mathematics in Lean, Chapter 5 §3 (Infinitely Many Primes), exercise 1. Avigad & Massot, Apache-2.0, commit dd6d752. -/
theorem mil_c05_s03_ex01 {m : ℕ} (h0 : m ≠ 0) (h1 : m ≠ 1) : 2 ≤ m := by
  have h_exists_k : ∃ k, m = k + 1 := by
    have h : ∃ k, m = k + 1 := by
      apply Nat.exists_eq_succ_of_ne_zero
      exact h0
    exact h
  
  have h_k_ne_zero : ∀ (k : ℕ), m = k + 1 → k ≠ 0 := by
    intro k hk
    by_contra h
    have h₂ : k = 0 := by simpa using h
    rw [h₂] at hk
    have h₃ : m = 1 := by
      simp [hk]
    exact h1 h₃
  
  have h_k_ge_one : ∀ (k : ℕ), m = k + 1 → 1 ≤ k := by
    intro k hk
    by_contra h
    have h₂ : k = 0 := by
      omega
    have h₃ : k ≠ 0 := h_k_ne_zero k hk
    exact h₃ h₂
  
  have h_main : 2 ≤ m := by
    obtain ⟨k, hk⟩ := h_exists_k
    have h₂ : 1 ≤ k := h_k_ge_one k hk
    have h₃ : 2 ≤ m := by
      have h₄ : m = k + 1 := hk
      have h₅ : 1 ≤ k := h₂
      omega
    exact h₃
  
  exact h_main
