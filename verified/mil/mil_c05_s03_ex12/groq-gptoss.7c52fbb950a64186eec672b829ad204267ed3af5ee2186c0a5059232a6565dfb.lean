import Mathlib

open BigOperators
open Finset

/-- Mathematics in Lean, Chapter 5 §3 (Infinitely Many Primes), exercise 12. Avigad & Massot, Apache-2.0, commit dd6d752. -/
theorem mil_c05_s03_ex12 (Q : ℕ → Prop) [DecidablePred Q] :
    (∃ n, ∀ k, Q k → k ≤ n) → ∃ s : Finset ℕ, ∀ k, Q k ↔ k ∈ s := by
  rintro ⟨n, hbound⟩
  refine ⟨(Finset.range (n + 1)).filter Q, ?_⟩
  intro k
  constructor
  · intro hkQ
    have hk_le : k ≤ n := hbound k hkQ
    have hk_lt : k < n + 1 := Nat.lt_succ_of_le hk_le
    have hk_mem_range : k ∈ Finset.range (n + 1) := (Finset.mem_range).2 hk_lt
    have : k ∈ (Finset.range (n + 1)).filter Q :=
      (Finset.mem_filter).2 ⟨hk_mem_range, hkQ⟩
    simpa using this
  · intro hk_mem
    rcases (Finset.mem_filter).1 hk_mem with ⟨_, hkQ⟩
    exact hkQ
