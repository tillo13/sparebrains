import Mathlib

open BigOperators
open Finset

/-- Mathematics in Lean, Chapter 5 §3 (Infinitely Many Primes), exercise 4. Avigad & Massot, Apache-2.0, commit dd6d752. -/
theorem mil_c05_s03_ex04 {α : Type*} [DecidableEq α] (r s t : Finset α) : (r ∪ s) ∩ (r ∪ t) = r ∪ s ∩ t := by
  ext x
  constructor
  · intro hx
    rcases mem_inter.1 hx with ⟨hx1, hx2⟩
    rcases mem_union.1 hx1 with hx1r | hx1s
    · exact mem_union.2 (Or.inl hx1r)
    · rcases mem_union.1 hx2 with hx2r | hx2t
      · exact mem_union.2 (Or.inl hx2r)
      · exact mem_union.2 (Or.inr (mem_inter.2 ⟨hx1s, hx2t⟩))
  · intro hx
    rcases mem_union.1 hx with hx1 | hx2
    · exact mem_inter.2 ⟨mem_union.2 (Or.inl hx1), mem_union.2 (Or.inl hx1)⟩
    · rcases mem_inter.1 hx2 with ⟨hx2s, hx2t⟩
      exact mem_inter.2 ⟨mem_union.2 (Or.inr hx2s), mem_union.2 (Or.inr hx2t)⟩
