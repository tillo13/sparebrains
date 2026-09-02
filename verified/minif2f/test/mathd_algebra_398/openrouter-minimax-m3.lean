import Mathlib

open scoped Nat
open scoped Real

/--
On planet Larky, 7 ligs = 4 lags, and 9 lags = 20 lugs. How many ligs are equivalent to 80 lugs? -/
theorem mathd_algebra_398 (a b c : ℝ) (h₀ : 0 < a ∧ 0 < b ∧ 0 < c) (h₁ : 9 * b = 20 * c)
    (h₂ : 7 * a = 4 * b) : 63 * a = 80 * c := by
  have hb : b ≠ 0 := (h₀.2.1).ne'
  have hc : c ≠ 0 := (h₀.2.2).ne'
  -- From h₂: b = 7a/4; substitute into h₁: 9*(7a/4) = 20c → 63a/4 = 20c → 63a = 80c
  -- More cleanly: 63a = 9*7a = 9*(4b) [using h₂ backwards] ... let's do it step by step.
  -- h₂ : 7a = 4b → multiply by 9: 63a = 36b
  -- h₁ : 9b = 20c → multiply by 4: 36b = 80c
  -- Chain: 63a = 36b = 80c
  have h₃ : 63 * a = 36 * b := by
    have := congrArg (fun x => 9 * x) h₂
    ring_nf at this; linarith [this]
  have h₄ : 36 * b = 80 * c := by
    have := congrArg (fun x => 4 * x) h₁
    ring_nf at this; linarith [this]
  linarith [h₃, h₄]
