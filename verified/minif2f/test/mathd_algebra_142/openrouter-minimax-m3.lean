import Mathlib

open scoped Nat
open scoped Real

/--
A line $\ell$ passes through the points $B(7,-1)$ and $C(-1,7)$.  The equation of this line can be written in the form $y=mx+b$; compute $m+b$. -/
theorem mathd_algebra_142 (m b : ℝ) (h₀ : m * 7 + b = -1) (h₁ : m * -1 + b = 7) : m + b = 5 := by
  have hsub : (m * 7 + b) - (m * -1 + b) = -1 - 7 := by
    rw [h₀, h₁]
  have hsimpl : m * 7 + b - (m * -1 + b) = -8 := by linarith
  have hcalc : m * 7 - m * -1 = -8 := by linarith
  have hm : m * 7 - m * -1 = -8 := by linarith
  have hmm : m * (7 - -1) = -8 := by
    linarith
  have hm' : m * 8 = -8 := by
    rw [sub_neg_eq_add] at hmm
    linarith
  have hmm' : m = -1 := by linarith
  linarith
