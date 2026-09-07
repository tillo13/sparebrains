import Mathlib

open BigOperators
open Finset

/-- Mathematics in Lean, Chapter 5 §3 (Infinitely Many Primes), exercise 12. Avigad & Massot, Apache-2.0, commit dd6d752. -/
theorem mil_c05_s03_ex12 (Q : ℕ → Prop) [DecidablePred Q] :
    (∃ n, ∀ k, Q k → k ≤ n) → ∃ s : Finset ℕ, ∀ k, Q k ↔ k ∈ s := by
  intro h
  rcases h with ⟨n, hn⟩
  let s := (range (n + 1)).filter Q
  use s
  intro k
  constructor
  · intro hQ
    have hle : k ≤ n := hn k hQ
    have hmem : k ∈ range (n + 1) := mem_range.mpr (Nat.lt_succ_of_le hle)
    exact mem_filter.mpr ⟨hmem, hQ⟩
  · intro hk
    exact (mem_filter.mp hk).2
