import Mathlib

open BigOperators
open Finset

/-- Mathematics in Lean, Chapter 5 §3 (Infinitely Many Primes), exercise 12. Avigad & Massot, Apache-2.0, commit dd6d752. -/
theorem mil_c05_s03_ex12 (Q : ℕ → Prop) [DecidablePred Q] :
    (∃ n, ∀ k, Q k → k ≤ n) → ∃ s : Finset ℕ, ∀ k, Q k ↔ k ∈ s := by
  intro h
  cases' h with n hn
  let s := Finset.filter Q (Finset.Icc 0 n)
  use s
  intro k
  constructor
  · intro hq
    have hkn : k ≤ n := hn k hq
    have hko : 0 ≤ k := Nat.zero_le k
    exact Finset.mem_filter.2 ⟨Finset.mem_Icc.mpr ⟨hko, hkn⟩, hq⟩
  · intro hks
    exact (Finset.mem_filter.1 hks).2
