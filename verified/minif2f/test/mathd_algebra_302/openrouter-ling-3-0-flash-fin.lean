import Mathlib

open scoped Nat
open scoped Real

/-- Evaluate $\left(\frac{i}{2}\right)^2$. -/
theorem mathd_algebra_302 : (Complex.I / 2) ^ 2 = -(1 / 4) := by
  simp [pow_two, Complex.I_sq, div_mul_div_comm, mul_comm, mul_left_comm, mul_assoc, div_self, mul_one, mul_two, two_mul]
  ring
