import Mathlib

/-- Natural Number Game (Lean 4), AdvMultiplication world, level 6: mul_right_eq_one. Restated over Mathlib's ℕ. Source: https://github.com/leanprover-community/NNG4/blob/main/Game/Levels/AdvMultiplication/L06mul_right_eq_one.lean, Apache-2.0. -/
theorem primer_advmultiplication_06_mul_right_eq_one (x y : ℕ) (h : x * y = 1) : x = 1 := by
  have h1 : x ∣ 1 := by
    use y
    linarith
  have h2 : x ≤ 1 := by
    exact Nat.le_of_dvd (by norm_num) h1
  interval_cases x <;> omega
