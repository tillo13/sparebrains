import Mathlib

open BigOperators
open Finset

/-- Mathematics in Lean, Chapter 5 §3 (Infinitely Many Primes), exercise 4. Avigad & Massot, Apache-2.0, commit dd6d752. -/
theorem mil_c05_s03_ex04 {α : Type*} [DecidableEq α] (r s t : Finset α) : (r ∪ s) ∩ (r ∪ t) = r ∪ s ∩ t := by
  ext x
  constructor
  · intro hx
    rcases mem_inter.1 hx with ⟨h1, h2⟩
    rcases mem_union.1 h1 with h1r | h1s
    · exact mem_union.2 (Or.inl h1r)
    rcases mem_union.1 h2 with h2r | h2t
    · exact mem_union.2 (Or.inl h2r)
    exact
      mem_union.2
        (Or.inr (mem_inter.2 ⟨h1s, h2t⟩))
  · intro hx
    rcases mem_union.1 hx with hx | hx
    · exact
        mem_inter.2
          ⟨mem_union.2 (Or.inl hx), mem_union.2 (Or.inl hx)⟩
    · rcases mem_inter.1 hx with ⟨hs, ht⟩
      exact
        mem_inter.2
          ⟨mem_union.2 (Or.inr hs), mem_union.2 (Or.inr ht)⟩
