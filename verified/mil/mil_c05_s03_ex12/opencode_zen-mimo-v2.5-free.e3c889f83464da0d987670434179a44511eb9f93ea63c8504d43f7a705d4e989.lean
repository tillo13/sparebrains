import Mathlib

open BigOperators
open Finset

/-- Mathematics in Lean, Chapter 5 §3 (Infinitely Many Primes), exercise 12. Avigad & Massot, Apache-2.0, commit dd6d752. -/
theorem mil_c05_s03_ex12 (Q : ℕ → Prop) [DecidablePred Q] :
    (∃ n, ∀ k, Q k → k ≤ n) → ∃ s : Finset ℕ, ∀ k, Q k ↔ k ∈ s := by
  intro ⟨n, hn⟩
  refine ⟨filter Q (range (n + 1)), fun k => ?_⟩
  constructor
  · intro hk
    have hk_range : k ≤ n := hn k hk
    rw [mem_filter, mem_range]
    exact ⟨by omega, hk⟩
  · intro hk
    exact (mem_filter.mp hk).2
