import Mathlib

open BigOperators
open Finset

/-- Mathematics in Lean, Chapter 5 §3 (Infinitely Many Primes), exercise 12. Avigad & Massot, Apache-2.0, commit dd6d752. -/
theorem mil_c05_s03_ex12 (Q : ℕ → Prop) [DecidablePred Q] :
    (∃ n, ∀ k, Q k → k ≤ n) → ∃ s : Finset ℕ, ∀ k, Q k ↔ k ∈ s := by
  rintro ⟨n, hn⟩
  use filter Q (range (n+1))
  intro k
  constructor
  · intro hQk
    have hle : k ≤ n := hn k hQk
    have hmem_range : k ∈ range (n+1) := by
      rw [mem_range]
      exact Nat.lt_succ_of_le hle
    exact mem_filter.2 ⟨hmem_range, hQk⟩
  · intro hmem
    exact mem_filter.1 hmem |>.2
