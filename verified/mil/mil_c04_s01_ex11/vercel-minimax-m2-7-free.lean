import Mathlib

open Set

/-- Mathematics in Lean, Chapter 4 §1 (Sets), exercise 11. Avigad & Massot, Apache-2.0, commit dd6d752. -/
theorem mil_c04_s01_ex11 {α I : Type*} (A : I → Set α) (s : Set α) : (s ∪ ⋂ i, A i) = ⋂ i, A i ∪ s := by
  ext x
  simp only [mem_union, mem_iInter]
  constructor
  · rintro (hx | hxA) i
    · exact Or.inr hx
    · exact Or.inl (hxA i)
  · intro hx
    by_cases hxs : x ∈ s
    · exact Or.inl hxs
    · right
      intro i
      exact (hx i).resolve_right hxs
