import Mathlib

open scoped Nat
open scoped Real

/--
If a snack-size tin of peaches has $40$ calories and is $2\%$ of a person's daily caloric requirement, how many calories fulfill a person's daily caloric requirement? -/
theorem mathd_algebra_24 (x : ℝ) (h₀ : x / 50 = 40) : x = 2000 := by
  calc
    x = 40 * 50 := by
      have := congrArg (fun t => t * 50) h₀
      simpa [div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc] using this
    _ = 2000 := by norm_num
