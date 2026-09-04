import Mathlib

open scoped Nat
open scoped Real

/--
On planet Larky, 7 ligs = 4 lags, and 9 lags = 20 lugs. How many ligs are equivalent to 80 lugs? -/
theorem mathd_algebra_398 (a b c : ℝ) (h₀ : 0 < a ∧ 0 < b ∧ 0 < c) (h₁ : 9 * b = 20 * c)
    (h₂ : 7 * a = 4 * b) : 63 * a = 80 * c := by
  have h₃ : 63 * a = 36 * b := by
    have h₃₁ : 7 * a = 4 * b := h₂
    have h₃₂ : 9 * (7 * a) = 9 * (4 * b) := by rw [h₃₁]
    -- Simplify both sides to get 63 * a = 36 * b
    ring_nf at h₃₂ ⊢
    linarith
  
  have h₄ : 36 * b = 80 * c := by
    have h₄₁ : 9 * b = 20 * c := h₁
    have h₄₂ : 4 * (9 * b) = 4 * (20 * c) := by rw [h₄₁]
    -- Simplify both sides to get 36 * b = 80 * c
    ring_nf at h₄₂ ⊢
    linarith
  
  have h₅ : 63 * a = 80 * c := by
    linarith
  
  rw [h₅]
  <;> norm_num
