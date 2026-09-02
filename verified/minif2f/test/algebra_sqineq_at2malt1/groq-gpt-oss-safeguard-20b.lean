import Mathlib

open scoped Nat
open scoped Real

theorem algebra_sqineq_at2malt1 (a : ℝ) : a * (2 - a) ≤ 1 := by
  have h1 : 1 - a * (2 - a) = (a - 1)^2 := by ring
  have h2 : 0 ≤ (a - 1)^2 := by
    exact sq_nonneg _
  have h3 : 0 ≤ 1 - a * (2 - a) := by
    simpa [h1] using h2
  exact sub_nonneg.mp h3
