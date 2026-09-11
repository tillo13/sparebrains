import Mathlib

open BigOperators
open Finset

/-- Mathematics in Lean, Chapter 5 §3 (Infinitely Many Primes), exercise 12. Avigad & Massot, Apache-2.0, commit dd6d752. -/
theorem mil_c05_s03_ex12 (Q : ℕ → Prop) [DecidablePred Q] :
    (∃ n, ∀ k, Q k → k ≤ n) → ∃ s : Finset ℕ, ∀ k, Q k ↔ k ∈ s := by
  intro ⟨n, hn⟩
  let s := (Finset.range (n + 1)).filter Q
  use s
  intro k
  constructor
  · intro hk
    have hkn : k ≤ n := hn k hk
    have hr : k ∈ Finset.range (n + 1) := by
      rw [Finset.mem_range]
      linarith
    exact Finset.mem_filter.mpr ⟨hr, hk⟩
  · intro hk
    exact (Finset.mem_filter.mp hk).2
