import Mathlib

open BigOperators
open Finset

/-- Mathematics in Lean, Chapter 5 §3 (Infinitely Many Primes), exercise 12. Avigad & Massot, Apache-2.0, commit dd6d752. -/
theorem mil_c05_s03_ex12 (Q : ℕ → Prop) [DecidablePred Q] :
    (∃ n, ∀ k, Q k → k ≤ n) → ∃ s : Finset ℕ, ∀ k, Q k ↔ k ∈ s := by
  rintro ⟨n, hn⟩
  use Finset.filter Q (range (n + 1))
  intro k
  constructor
  · intro hk
    have hkn : k ≤ n := hn k hk
    exact Finset.mem_filter.2 ⟨Finset.mem_range.2 (Nat.lt_succ_iff.2 hkn), hk⟩
  · intro hk
    exact Finset.mem_filter.1 hk |>.2
