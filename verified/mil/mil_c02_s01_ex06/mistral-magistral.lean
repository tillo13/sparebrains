import Mathlib

/-- Mathematics in Lean, Chapter 2 §1 (Calculating), exercise 6. Avigad & Massot, Apache-2.0, commit dd6d752. -/
theorem mil_c02_s01_ex06 (a b c d : ℝ) (hyp : c = b * a - d) (hyp' : d = a * b) : c = 0 := by
  have h1 : c = b * a - a * b := by
    rw [hyp, hyp']
  have h2 : b * a - a * b = 0 := by
    ring
  rw [h1, h2]
