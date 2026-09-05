import Mathlib

open scoped Nat
open scoped Real

/-- If $n = 11$, then what is $\left(\frac{1}{4}\right)^{n+1} \cdot 2^{2n}$? -/
theorem mathd_algebra_314 (n : ℕ) (h₀ : n = 11) : (1 / 4 : ℚ) ^ (n + 1) * 2 ^ (2 * n) = 1 / 4 := by
  rw [h₀] -- Substitute the given value of n into the expression
  -- The goal becomes: (1 / 4 : ℚ) ^ (11 + 1) * 2 ^ (2 * 11) = 1 / 4
  norm_num -- Evaluate all numerical expressions in the goal
  -- This tactic performs the arithmetic:
  -- (1 / 4 : ℚ) ^ (11 + 1) becomes (1 / 4 : ℚ) ^ 12
  -- 2 ^ (2 * 11) becomes 2 ^ 22
  -- Then it calculates (1/4)^12 * 2^22:
  -- (1/4)^12 = 1 / 4^12 = 1 / (2^2)^12 = 1 / 2^24
  -- So the expression is (1 / 2^24) * 2^22 = 2^22 / 2^24
  -- Which simplifies to 1 / 2^(24 - 22) = 1 / 2^2 = 1 / 4.
  -- `norm_num` handles all these steps automatically.
