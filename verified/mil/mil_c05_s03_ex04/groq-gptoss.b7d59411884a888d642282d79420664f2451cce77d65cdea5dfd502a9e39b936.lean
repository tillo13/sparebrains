import Mathlib

open BigOperators
open Finset

/-- Mathematics in Lean, Chapter 5 §3 (Infinitely Many Primes), exercise 4. Avigad & Massot, Apache-2.0, commit dd6d752. -/
theorem mil_c05_s03_ex04 {α : Type*} [DecidableEq α] (r s t : Finset α) : (r ∪ s) ∩ (r ∪ t) = r ∪ s ∩ t := by
  ext x
  constructor
  · intro hx
    rcases Finset.mem_inter.1 hx with ⟨hxs, hxt⟩
    rcases Finset.mem_union.1 hxs with hxr | hxs
    · exact Finset.mem_union.2 (Or.inl hxr)
    · rcases Finset.mem_union.1 hxt with hxr' | hxt
      · exact Finset.mem_union.2 (Or.inl hxr')
      · exact
          Finset.mem_union.2
            (Or.inr (Finset.mem_inter.2 ⟨hxs, hxt⟩))
  · intro hx
    rcases Finset.mem_union.1 hx with hx | hx
    · exact
        Finset.mem_inter.2
          ⟨Finset.mem_union.2 (Or.inl hx), Finset.mem_union.2 (Or.inl hx)⟩
    · rcases Finset.mem_inter.1 hx with ⟨hs, ht⟩
      exact
        Finset.mem_inter.2
          ⟨Finset.mem_union.2 (Or.inr hs), Finset.mem_union.2 (Or.inr ht)⟩
