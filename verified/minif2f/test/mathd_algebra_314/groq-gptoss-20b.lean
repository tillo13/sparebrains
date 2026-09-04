import Mathlib

open scoped Nat
open scoped Real

/-- If $n = 11$, then what is $\left(\frac{1}{4}\right)^{n+1} \cdot 2^{2n}$? -/
theorem mathd_algebra_314 (n : ℕ) (h₀ : n = 11) : (1 / 4 : ℚ) ^ (n + 1) * 2 ^ (2 * n) = 1 / 4 := by
  have h : (1 / 4 : ℚ) ^ 12 * 2 ^ 22 = 1 / 4 := by
    norm_num
  simpa [h₀] using h
