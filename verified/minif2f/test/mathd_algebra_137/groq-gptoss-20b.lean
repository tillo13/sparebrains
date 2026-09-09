import Mathlib

open scoped Nat
open scoped Real

/--
Because of redistricting, Liberty Middle School's enrollment increased to 598 students. This is an increase of $4\%$ over last year's enrollment. What was last year's enrollment? -/
theorem mathd_algebra_137 (x : ℕ) (h₀ : ↑x + (4 : ℝ) / (100 : ℝ) * ↑x = 598) : x = 575 := by
  -- Rewrite the hypothesis as a product
  have h1 : (x : ℝ) * (1 + (4 : ℝ) / 100) = 598 := by
    simpa [mul_add, one_mul, mul_comm, mul_left_comm, mul_assoc] using h₀
  -- Solve for x
  have h2 : (x : ℝ) = 598 / (1 + (4 : ℝ) / 100) := by
    have : (x : ℝ) * (1 + (4 : ℝ) / 100) = 598 := h1
    exact (eq_div_iff_mul_eq (by norm_num : (1 + (4 : ℝ) / 100) ≠ 0)).mpr this
  -- Simplify the denominator
  have h3 : (1 + (4 : ℝ) / 100) = 26 / 25 := by norm_num
  have h4 : (x : ℝ) = 598 / (26 / 25) := by
    simpa [h3] using h2
  have h5 : (x : ℝ) = 598 * 25 / 26 := by
    simpa [div_eq_mul_inv, inv_div, mul_comm, mul_left_comm, mul_assoc] using h4
  -- Evaluate the expression
  have hx : (x : ℝ) = 575 := by
    norm_num at h5
    exact h5
  -- Cast back to ℕ
  exact_mod_cast hx
