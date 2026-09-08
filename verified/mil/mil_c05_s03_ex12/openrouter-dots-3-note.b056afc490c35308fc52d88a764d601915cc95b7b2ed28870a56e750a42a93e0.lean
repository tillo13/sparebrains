import Mathlib

open BigOperators
open Finset

/-- Mathematics in Lean, Chapter 5 §3 (Infinitely Many Primes), exercise 12. Avigad & Massot, Apache-2.0, commit dd6d752. -/
theorem mil_c05_s03_ex12 (Q : ℕ → Prop) [DecidablePred Q] :
    (∃ n, ∀ k, Q k → k ≤ n) → ∃ s : Finset ℕ, ∀ k, Q k ↔ k ∈ s := by
  intro h
  rcases h with ⟨n, hn⟩
  let s : Finset ℕ := (Finset.range (n+1)).filter Q
  refine ⟨s, ?_⟩
  intro k
  constructor
  · intro hk
    have hk_n : k ≤ n := hn k hk
    have h_mem : k ∈ Finset.range (n+1) := Finset.mem_range.mpr (Nat.lt_succ_of_le hk_n)
    exact Finset.mem_filter.mpr ⟨h_mem, hk⟩
  · intro h_mem
    rcases Finset.mem_filter.mp h_mem with ⟨_, hk⟩
    exact hk
