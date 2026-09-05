import Mathlib

open BigOperators
open Finset

/-- Mathematics in Lean, Chapter 5 §3 (Infinitely Many Primes), exercise 6. Avigad & Massot, Apache-2.0, commit dd6d752. -/
theorem mil_c05_s03_ex06 {α : Type*} [DecidableEq α] (r s t : Finset α) : (r \ s) \ t = r \ (s ∪ t) := by
  ext x
  constructor
  · intro hx
    rcases mem_sdiff.1 hx with ⟨hxRS, hxNotT⟩
    rcases mem_sdiff.1 hxRS with ⟨hxR, hxNotS⟩
    have hxNotUnion : x ∉ s ∪ t := by
      intro hxUnion
      rcases mem_union.1 hxUnion with hxS | hxT
      · exact hxNotS hxS
      · exact hxNotT hxT
    exact mem_sdiff.2 ⟨hxR, hxNotUnion⟩
  · intro hx
    rcases mem_sdiff.1 hx with ⟨hxR, hxNotUnion⟩
    have hxNotS : x ∉ s := by
      intro hxS
      apply hxNotUnion
      exact mem_union.2 (Or.inl hxS)
    have hxNotT : x ∉ t := by
      intro hxT
      apply hxNotUnion
      exact mem_union.2 (Or.inr hxT)
    have hxRS : x ∈ r \ s := mem_sdiff.2 ⟨hxR, hxNotS⟩
    exact mem_sdiff.2 ⟨hxRS, hxNotT⟩
