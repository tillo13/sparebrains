import Mathlib

/-- Mathematics in Lean, Chapter 3 §3 (Negation), exercise 3. Avigad & Massot, Apache-2.0, commit dd6d752. -/
theorem mil_c03_s03_ex03 (a b : ℝ) (f : ℝ → ℝ) (h : Monotone f) (h' : f a < f b) : a < b := by
  by_contra hnot
  have hle : b ≤ a := by
    have : a < b ∨ b ≤ a := lt_or_ge a b
    cases this with
    | inl hlt => exact (hnot hlt).elim
    | inr hle => exact hle
  have hfb_le_fa : f b ≤ f a := h hle
  have hcontr : f a < f a := lt_of_lt_of_le h' hfb_le_fa
  exact (lt_irrefl _ hcontr)
