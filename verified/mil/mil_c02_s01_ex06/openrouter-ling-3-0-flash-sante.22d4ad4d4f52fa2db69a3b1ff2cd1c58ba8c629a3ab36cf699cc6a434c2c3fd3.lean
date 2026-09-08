import Mathlib

/-- Mathematics in Lean, Chapter 2 §1 (Calculating), exercise 6. Avigad & Massot, Apache-2.0, commit dd6d752. -/
theorem mil_c02_s01_ex06 (a b c d : ℝ) (hyp : c = b * a - d) (hyp' : d = a * b) : c = 0 := by
  rw [hyp'] at hyp   -- substitute d = a*b into hyp
  -- now hyp : c = b*a - a*b
  rw [mul_comm b a] at hyp
  -- now hyp : c = a*b - a*b
  simp [hyp]
  -- goal: c = 0, simp uses hyp : c = a*b - a*b to rewrite c to a*b - a*b
  -- goal becomes: a*b - a*b = 0, which is true by sub_self
