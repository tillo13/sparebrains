import Mathlib

open scoped Nat
open scoped Real

/-- Given the equations $3x+y=17,5y+z=14$ and $3x+5z=41$, what is the value of the sum $x+y+z$? -/
theorem mathd_algebra_427 (x y z : ℝ) (h₀ : 3 * x + y = 17) (h₁ : 5 * y + z = 14)
    (h₂ : 3 * x + 5 * z = 41) : x + y + z = 12 := by
  have h_sum : (3*x + y) + (5*y + z) + (3*x + 5*z) = (17:ℝ) + 14 + 41 := by
    rw [h₀, h₁, h₂]
  have h_left : (3*x + y) + (5*y + z) + (3*x + 5*z) = 6*(x + y + z) := by ring
  have h_right : (17:ℝ) + 14 + 41 = 72 := by norm_num
  have h_eq : 6*(x + y + z) = 72 := by
    calc
      6*(x + y + z) = (3*x + y) + (5*y + z) + (3*x + 5*z) := by rw [h_left]
      _ = (17:ℝ) + 14 + 41 := by rw [h_sum]
      _ = 72 := by rw [h_right]
  have h6 : (6:ℝ) ≠ 0 := by norm_num
  have h_mul : 6 * (x + y + z) = 6 * (12:ℝ) := by
    rw [h_eq]
    norm_num
  exact mul_left_cancel₀ h6 h_mul
