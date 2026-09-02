import Mathlib

open Finset

/-- Mathematics in Lean, Chapter 6 §2 (Counting Arguments), exercise 3. Avigad & Massot, Apache-2.0, commit dd6d752. -/
theorem mil_c06_s02_ex03 {n : ℕ} (A : Finset ℕ)
    (hA : #(A) = n + 1)
    (hA' : A ⊆ range (2 * n)) :
    ∃ m ∈ A, ∃ k ∈ A, Nat.Coprime m k := by
  sorry
