import Mathlib

open scoped Nat
open scoped Real

/-- If $3a + b + c = -3, a+3b+c = 9, a+b+3c = 19$, then find $abc$. -/
theorem mathd_algebra_338 (a b c : ℝ) (h₀ : 3 * a + b + c = -3) (h₁ : a + 3 * b + c = 9)
    (h₂ : a + b + 3 * c = 19) : a * b * c = -56 := by
  -- Add all three equations: 5a + 5b + 5c = 25, so a + b + c = 5
  have h_sum : a + b + c = 5 := by
    have : 5 * a + 5 * b + 5 * c = 25 := by linarith [h₀, h₁, h₂]
    linarith [this] -- or field_simp
  -- From h₀ and h_sum: 3a + b + c = -3 and a + b + c = 5
  -- Subtract: 2a = -8, so a = -4
  have ha : a = -4 := by
    have : 2 * a = -8 := by linarith [h₀, h_sum]
    linarith [this]
  -- From h₁ and h_sum: a + 3b + c = 9 and a + b + c = 5
  -- Subtract: 2b = 4, so b = 2
  have hb : b = 2 := by
    have : 2 * b = 4 := by linarith [h₁, h_sum]
    linarith [this]
  -- From h₂ and h_sum: a + b + 3c = 19 and a + b + c = 5
  -- Subtract: 2c = 14, so c = 7
  have hc : c = 7 := by
    have : 2 * c = 14 := by linarith [h₂, h_sum]
    linarith [this]
  -- Now compute abc
  rw [ha, hb, hc]
  ring
