import Mathlib

open scoped Nat
open scoped Real

/--
If a snack-size tin of peaches has $40$ calories and is $2\%$ of a person's daily caloric requirement, how many calories fulfill a person's daily caloric requirement? -/
theorem mathd_algebra_24 (x : ℝ) (h₀ : x / 50 = 40) : x = 2000 := by
  -- Use h₀ to rewrite
  -- h₀ says x / 50 = 40
  -- We want x = 2000
  -- Note: 2000 = 40 * 50
  -- So we need to show x = 40 * 50
  -- From h₀: x / 50 = 40, so x = 40 * 50 (multiply both sides by 50)
  
  -- One way: use the fact that x / 50 * 50 = x (for 50 ≠ 0)
  have h : x = (x / 50) * 50 := by
    -- This is true because division by 50 and multiplication by 50 cancel
    -- In Lean, we can prove this with field_simp
    field_simp
  rw [h, h₀]
  norm_num
