import Mathlib

open scoped Nat
open scoped Real

/--
If $n$ is a multiple of three, what is the remainder when $(n + 4) + (n + 6) + (n + 8)$ is divided by $9$? -/
theorem mathd_numbertheory_582 (n : ℕ) (h₀ : 0 < n) (h₁ : 3 ∣ n) :
    (n + 4 + (n + 6) + (n + 8)) % 9 = 0 := by
  have h : n + 4 + (n + 6) + (n + 8) = 3 * n + 18 := by ring
  rw [h]
  obtain ⟨k, hk⟩ := h₁
  rw [hk]
  ring_nf
  rw [show 18 = 2 * 9 from (by ring : (18 : ℕ) = 2 * 9)]
  rw [show (2 * 9 + k * 9 : ℕ) = 9 * (2 + k) from (by ring : (2 * 9 + k * 9 : ℕ) = 9 * (2 + k))]
  rw [Nat.mul_mod_right]
