import Mathlib

open scoped Nat
open scoped Real

/-- If $f(x)=ax^4-bx^2+x+5$ and $f(-3)=2,$ then what is the value of $f(3)$? -/
theorem mathd_algebra_246 (a b : ℝ) (f : ℝ → ℝ) (h₀ : ∀ x, f x = a * x ^ 4 - b * x ^ 2 + x + 5)
    (h₂ : f (-3) = 2) : f 3 = 8 := by
  rw [h₀] at h₂ ⊢
  -- Now h₂ : a * (-3) ^ 4 - b * (-3) ^ 2 + (-3) + 5 = 2
  -- Goal: a * 3 ^ 4 - b * 3 ^ 2 + 3 + 5 = 8
  -- Simplify powers: (-3)^4 = 81, 3^4 = 81, (-3)^2 = 9, 3^2 = 9.
  -- So h₂ : 81a - 9b - 3 + 5 = 2 => 81a - 9b + 2 = 2 => 81a - 9b = 0.
  -- Goal: 81a - 9b + 3 + 5 = 8 => 81a - 9b + 8 = 8.
  -- So we need to show 81a - 9b = 0.
  -- We can use `ring` or `linarith`.
  -- Let's try `ring` first. But `ring` might not solve it directly because of the specific numbers.
  -- Actually, `ring` can solve equalities between polynomials. But here we have specific numbers.
  -- We can use `linarith` after simplifying.
  -- Or we can compute: `norm_num` at h₂ to get 81*a - 9*b + 2 = 2, then `linarith`.
  norm_num at h₂
  -- h₂ : 81 * a - 9 * b + 2 = 2
  -- Goal: 81 * a - 9 * b + 8 = 8
  linarith
