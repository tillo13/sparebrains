import Mathlib

/-- Natural Number Game (Lean 4), Power world, level 9: add_sq. Restated over Mathlib's ℕ. Source: https://github.com/leanprover-community/NNG4/blob/main/Game/Levels/Power/L09add_sq.lean, Apache-2.0. -/
theorem primer_power_09_add_sq (a b : ℕ) : (a + b) ^ 2 = a ^ 2 + b ^ 2 + 2 * a * b := by
  have h_main : (a + b) ^ 2 = a ^ 2 + b ^ 2 + 2 * a * b := by
    ring
    <;> simp [add_assoc, add_comm, add_left_comm, mul_comm, mul_assoc, mul_left_comm]
    <;> ring
    <;> omega
  
  apply h_main
