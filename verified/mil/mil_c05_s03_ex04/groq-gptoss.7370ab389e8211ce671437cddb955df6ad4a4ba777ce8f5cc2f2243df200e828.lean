import Mathlib

open BigOperators
open Finset

/-- Mathematics in Lean, Chapter 5 §3 (Infinitely Many Primes), exercise 4. Avigad & Massot, Apache-2.0, commit dd6d752. -/
theorem mil_c05_s03_ex04 {α : Type*} [DecidableEq α] (r s t : Finset α) : (r ∪ s) ∩ (r ∪ t) = r ∪ s ∩ t := by
  ext x
  constructor
  · intro hx
    rcases mem_inter.1 hx with ⟨hxs, hxt⟩
    rcases mem_union.1 hxs with hxr | hxs
    · exact mem_union.2 (Or.inl hxr)
    rcases mem_union.1 hxt with hxr' | hxt
    · exact mem_union.2 (Or.inl hxr')
    · exact
        mem_union.2
          (Or.inr (mem_inter.2 ⟨hxs, hxt⟩))
  · intro hx
    rcases mem_union.1 hx with hxr | hst
    · exact
        mem_inter.2
          ⟨mem_union.2 (Or.inl hxr), mem_union.2 (Or.inl hxr)⟩
    rcases mem_inter.1 hst with ⟨hs, ht⟩
    exact
      mem_inter.2
        ⟨mem_union.2 (Or.inr hs), mem_union.2 (Or.inr ht)⟩
