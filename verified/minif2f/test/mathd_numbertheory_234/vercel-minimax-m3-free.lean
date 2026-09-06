import Mathlib

open scoped Nat
open scoped Real

/--
When the two-digit integer $``\text{AB}"$ is cubed, the value is $912,\!673$. What is $A + B$? -/
theorem mathd_numbertheory_234 (a b : ℕ) (h₀ : 1 ≤ a ∧ a ≤ 9 ∧ b ≤ 9)
    (h₁ : (10 * a + b) ^ 3 = 912673) : a + b = 16 := by
  obtain ⟨ha1, ha2, hb⟩ := h₀
  have hn : 10 * a + b ≤ 99 := by omega
  have hn' : 10 * a + b ≥ 10 := by omega
  have hk : 10 * a + b = 97 := by
    have h1' : (10 * a + b) ^ 3 ≤ 99 ^ 3 := by
      gcongr
    have h2' : (10 * a + b) ^ 3 ≥ 10 ^ 3 := by
      gcongr
    interval_cases n : (10 * a + b) <;> omega
  rw [hk] at h₁
  norm_num at h₁
  omega
