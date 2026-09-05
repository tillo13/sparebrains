import Mathlib

/-- Mathematics in Lean, Chapter 3 §1 (Implication and the Universal Quantifier), exercise 5. Avigad & Massot, Apache-2.0, commit dd6d752. -/
theorem mil_c03_s01_ex05 (f : ℝ → ℝ) {c : ℝ} (mf : Monotone f) (nnc : 0 ≤ c) : Monotone fun x ↦ c * f x := by
  intro a b hab
  have h₁ : f a ≤ f b := mf hab
  have h₂ : c * f a ≤ c * f b := mul_le_mul_of_nonneg_left h₁ nnc
  exact h₂
