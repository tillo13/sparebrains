import Mathlib

open scoped Nat
open scoped Real

/-- What is the sum of the two values of $x$ for which $(x+3)^2 = 121$? -/
theorem mathd_algebra_215 (S : Finset ℝ) (h₀ : ∀ x : ℝ, x ∈ S ↔ (x + 3) ^ 2 = 121) :
    ∑ k ∈ S, k = -6 := by
  have h₁ : S = {8, -14} := by
    apply Finset.ext
    intro x
    simp only [Finset.mem_insert, Finset.mem_singleton]
    rw [h₀ x]
    constructor
    · intro h
      have h₂ : (x + 3 - 11) * (x + 3 + 11) = 0 := by
        calc
          (x + 3 - 11) * (x + 3 + 11) = (x + 3) ^ 2 - 121 := by ring
          _ = 0 := by rw [h]; norm_num
      have h₃ : x + 3 - 11 = 0 ∨ x + 3 + 11 = 0 := by
        exact eq_zero_or_eq_zero_of_mul_eq_zero h₂
      cases h₃ with
      | inl h₃ =>
          left
          linarith
      | inr h₃ =>
          right
          linarith
    · rintro (rfl | rfl)
      · norm_num
      · norm_num
  rw [h₁]
  rw [Finset.sum_pair (show (8 : ℝ) ≠ -14 by norm_num)]
  norm_num
