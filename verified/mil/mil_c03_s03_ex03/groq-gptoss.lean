import Mathlib

/-- Mathematics in Lean, Chapter 3 §3 (Negation), exercise 3. Avigad & Massot, Apache-2.0, commit dd6d752. -/
theorem mil_c03_s03_ex03 (a b : ℝ) (f : ℝ → ℝ) (h : Monotone f) (h' : f a < f b) : a < b := by
  by_contra hnot
  have hba : b ≤ a := le_of_not_gt (by
    simpa [gt_iff_lt] using hnot)
  have hfa : f a < f a := lt_of_lt_of_le h' (h hba)
  exact (lt_irrefl _ hfa)
