import Mathlib

open BigOperators
open Finset

/-- Mathematics in Lean, Chapter 5 §3 (Infinitely Many Primes), exercise 12. Avigad & Massot, Apache-2.0, commit dd6d752. -/
theorem mil_c05_s03_ex12 (Q : ℕ → Prop) [DecidablePred Q] :
    (∃ n, ∀ k, Q k → k ≤ n) → ∃ s : Finset ℕ, ∀ k, Q k ↔ k ∈ s := by
  intro h
  rcases h with ⟨n, hn⟩
  refine ⟨Finset.filter (fun k => Q k) (Finset.range (n+1)), ?_⟩
  intro k
  constructor
  · intro hk
    have hk_le : k ≤ n := hn k hk
    have hk_mem : k ∈ Finset.range (n+1) := by
      rw [Finset.mem_range]
      omega
    rw [Finset.mem_filter]
    exact ⟨hk_mem, hk⟩
  · intro hk
    rw [Finset.mem_filter] at hk
    exact hk.2
