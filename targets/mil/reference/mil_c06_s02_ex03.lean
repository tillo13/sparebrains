import Mathlib

open Finset

/-- Mathematics in Lean, Chapter 6 §2 (Counting Arguments), exercise 3. Avigad & Massot, Apache-2.0, commit dd6d752. -/
theorem mil_c06_s02_ex03 {n : ℕ} (A : Finset ℕ)
    (hA : #(A) = n + 1)
    (hA' : A ⊆ range (2 * n)) :
    ∃ m ∈ A, ∃ k ∈ A, Nat.Coprime m k := by
  have : ∃ t ∈ range n, 1 < #({u ∈ A | u / 2 = t}) := by
    apply exists_lt_card_fiber_of_mul_lt_card_of_maps_to
    · intro u hu
      specialize hA' hu
      simp only [mem_range] at *
      exact Nat.div_lt_of_lt_mul hA'
    · simp [hA]
  rcases this with ⟨t, ht, ht'⟩
  simp only [one_lt_card, mem_filter] at ht'
  rcases ht' with ⟨m, ⟨hm, hm'⟩, k, ⟨hk, hk'⟩, hmk⟩
  use m, hm, k, hk
  have : m = k + 1 ∨ k = m + 1 := by omega
  rcases this with h | h <;> simp [h]
