import Mathlib

open scoped Nat
open scoped Real

/-- Five plus $500\%$ of $10$ is the same as $110\%$ of what number? -/
theorem mathd_algebra_400 (x : ℝ) (h₀ : 5 + 500 / 100 * 10 = 110 / 100 * x) : x = 50 := by
  have h1 : (5 : ℝ) + (500 / 100) * 10 = (110 / 100) * x := h₀
  field_simp [div_eq_mul_inv] at h1
  have h2 : (5500 : ℝ) = 110 * x := by
    have h := h1
    norm_num at h
    exact h
  have hx : x = (5500 : ℝ) / 110 :=
    (eq_div_iff_mul_eq (by norm_num : (110 : ℝ) ≠ 0)).mpr (by
      simpa [mul_comm] using h2.symm)
  calc
    x = (5500 : ℝ) / 110 := hx
    _ = 50 := by norm_num
