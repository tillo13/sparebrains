import Mathlib

open scoped Nat
open scoped Real

/-- The four-digit number $\underline{374n}$ is divisible by 18. Find the units digit $n$. -/
theorem mathd_numbertheory_1124 (n : ℕ) (h₀ : n ≤ 9) (h₁ : 18 ∣ 374 * 10 + n) : n = 4 := by
  obtain ⟨k, hk⟩ := h₁
  have hk' : 18 * k = 3740+n := by linarith
  have hkl : k ≤ 208 := by
    nlinarith
  have hkn : 207 ≤ k := by
    omega
  interval_cases k <;> omega
