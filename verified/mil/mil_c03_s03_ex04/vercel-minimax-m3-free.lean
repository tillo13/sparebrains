import Mathlib

/-- Mathematics in Lean, Chapter 3 §3 (Negation), exercise 4. Avigad & Massot, Apache-2.0, commit dd6d752. -/
theorem mil_c03_s03_ex04 (a b : ℝ) (f : ℝ → ℝ) (h : a ≤ b) (h' : f b < f a) : ¬Monotone f := by
  intro hM
  have h₁ : f a ≤ f b := hM h
  have h₂ : f b < f a := h'
  exact (lt_irrefl _ (h₁.trans_lt h₂))
