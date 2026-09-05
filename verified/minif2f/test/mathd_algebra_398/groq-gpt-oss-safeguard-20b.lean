import Mathlib

open scoped Nat
open scoped Real

/--
On planet Larky, 7 ligs = 4 lags, and 9 lags = 20 lugs. How many ligs are equivalent to 80 lugs? -/
theorem mathd_algebra_398 (a b c : ℝ) (h₀ : 0 < a ∧ 0 < b ∧ 0 < c) (h₁ : 9 * b = 20 * c)
    (h₂ : 7 * a = 4 * b) : 63 * a = 80 * c := by
  have h₂' : 63 * a = 36 * b := by
    calc
      63 * a = 9 * (7 * a) := by ring
      _ = 9 * (4 * b) := by simpa [h₂]
      _ = 36 * b := by ring
  have h₁' : 36 * b = 80 * c := by
    calc
      36 * b = 4 * (9 * b) := by ring
      _ = 4 * (20 * c) := by simpa [h₁]
      _ = 80 * c := by ring
  exact h₂'.trans h₁'
