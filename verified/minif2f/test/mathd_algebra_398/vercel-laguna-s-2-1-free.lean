import Mathlib

open scoped Nat
open scoped Real

/--
On planet Larky, 7 ligs = 4 lags, and 9 lags = 20 lugs. How many ligs are equivalent to 80 lugs? -/
theorem mathd_algebra_398 (a b c : ℝ) (h₀ : 0 < a ∧ 0 < b ∧ 0 < c) (h₁ : 9 * b = 20 * c)
    (h₂ : 7 * a = 4 * b) : 63 * a = 80 * c := by
  have h : 9 * b = 20 * c := h₁
  have h' : 7 * a = 4 * b := h₂
  have : 63 * a = 80 * c := by
    calc
      63 * a = 9 * (7 * a) := by ring
      _ = 9 * (4 * b) := by rw [h']
      _ = 36 * b := by ring
      _ = 4 * (9 * b) := by ring
      _ = 4 * (20 * c) := by rw [h]
      _ = 80 * c := by ring
  exact this
