import Mathlib

open scoped Nat
open scoped Real

/--
When the two-digit integer $``\text{AB}"$ is cubed, the value is $912,\!673$. What is $A + B$? -/
theorem mathd_numbertheory_234 (a b : ℕ) (h₀ : 1 ≤ a ∧ a ≤ 9 ∧ b ≤ 9)
    (h₁ : (10 * a + b) ^ 3 = 912673) : a + b = 16 := by
  have h97 : (97 : ℕ)^3 = 912673 := by norm_num
  rw [← h97] at h₁
  have h_eq : 10 * a + b = 97 := by
    apply pow_left_injective (by decide : 3 ≠ 0)
    exact h₁
  omega
