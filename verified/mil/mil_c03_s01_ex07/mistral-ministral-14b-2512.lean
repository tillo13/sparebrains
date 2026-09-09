import Mathlib

/-- Mathematics in Lean, Chapter 3 §1 (Implication and the Universal Quantifier), exercise 7. Avigad & Massot, Apache-2.0, commit dd6d752. -/
theorem mil_c03_s01_ex07 (f g : ℝ → ℝ) (mf : Monotone f) (mg : Monotone g) : Monotone fun x ↦ f (g x) := by
  intro x₁ x₂ hx
  have hg : g x₁ ≤ g x₂ := mg hx
  have hf : f (g x₁) ≤ f (g x₂) := mf hg
  exact hf
