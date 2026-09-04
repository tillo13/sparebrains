import Mathlib

open scoped Nat
open scoped Real

theorem induction_1pxpownlt1pnx (x : ℝ) (n : ℕ) (h₀ : -1 < x) (h₁ : 0 < n) :
    1 + ↑n * x ≤ (1 + x) ^ (n : ℕ) := by
  have hx : (-2 : ℝ) ≤ x := by
    have : (-1 : ℝ) < x := h₀
    linarith
  simpa using (one_add_mul_le_pow hx n)
