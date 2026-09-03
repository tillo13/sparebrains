import Mathlib

open BigOperators
open Finset

/-- Mathematics in Lean, Chapter 5 §3 (Infinitely Many Primes), exercise 12. Avigad & Massot, Apache-2.0, commit dd6d752. -/
theorem mil_c05_s03_ex12 (Q : ℕ → Prop) [DecidablePred Q] :
    (∃ n, ∀ k, Q k → k ≤ n) → ∃ s : Finset ℕ, ∀ k, Q k ↔ k ∈ s := by
  intro h
  rcases h with ⟨n, hn⟩
  refine ⟨Finset.filter Q (Finset.range (n + 1)), ?_⟩
  intro k
  constructor
  · intro hk
    have hk_le : k ≤ n := hn k hk
    have hk_lt : k < n + 1 := Nat.lt_succ_of_le hk_le
    have hk_mem : k ∈ Finset.range (n + 1) := Finset.mem_range.mpr hk_lt
    exact Finset.mem_filter.mpr ⟨hk_mem, hk⟩
  · intro hk
    rcases Finset.mem_filter.mp hk with ⟨hk_mem, hkQ⟩
    have hk_lt : k < n + 1 := Finset.mem_range.mp hk_mem
    have _ : k ≤ n := Nat.le_of_lt_succ hk_lt
    exact hkQ
