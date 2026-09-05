import Mathlib

open scoped Nat
open scoped Real

/-- Let $f(x) = 2x-3$ and $g(x) = x+1$. What is the value of $g(f(5)-1)$? -/
theorem mathd_algebra_346 (f g : ℝ → ℝ) (h₀ : ∀ x, f x = 2 * x - 3) (h₁ : ∀ x, g x = x + 1) :
    g (f 5 - 1) = 7 := by
  have h_f5 : f 5 = 2 * 5 - 3 := h₀ 5
  have h_f5_simplified : f 5 = 7 := by
    rw [h_f5]
    norm_num
  have h_g_arg : g (f 5 - 1) = g (7 - 1) := by
    rw [h_f5_simplified]
  have h_g_arg_simplified : g (f 5 - 1) = g 6 := by
    rw [h_g_arg]
    norm_num
  have h_g6 : g 6 = 6 + 1 := h₁ 6
  have h_g6_simplified : g 6 = 7 := by
    rw [h_g6]
    norm_num
  rw [h_g_arg_simplified, h_g6_simplified]
