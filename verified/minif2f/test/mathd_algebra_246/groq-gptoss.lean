import Mathlib

open scoped Nat
open scoped Real

/-- If $f(x)=ax^4-bx^2+x+5$ and $f(-3)=2,$ then what is the value of $f(3)$? -/
theorem mathd_algebra_246 (a b : ℝ) (f : ℝ → ℝ) (h₀ : ∀ x, f x = a * x ^ 4 - b * x ^ 2 + x + 5)
    (h₂ : f (-3) = 2) : f 3 = 8 := by
  have h3 : f 3 = a * (3 : ℝ) ^ 4 - b * (3 : ℝ) ^ 2 + 3 + 5 := h₀ 3
  have hneg : f (-3) = a * (-3 : ℝ) ^ 4 - b * (-3 : ℝ) ^ 2 + (-3) + 5 := h₀ (-3)
  have hcalc : f 3 = f (-3) + 6 := by
    calc
      f 3 = a * (3 : ℝ) ^ 4 - b * (3 : ℝ) ^ 2 + 3 + 5 := h3
      _ = a * (-3 : ℝ) ^ 4 - b * (-3 : ℝ) ^ 2 + (-3) + 5 + 6 := by
        ring
      _ = f (-3) + 6 := by
        simpa [hneg] using rfl
  calc
    f 3 = f (-3) + 6 := hcalc
    _ = 2 + 6 := by
      simpa [h₂]
    _ = 8 := by
      norm_num
