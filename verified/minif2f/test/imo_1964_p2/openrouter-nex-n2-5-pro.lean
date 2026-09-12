import Mathlib

open scoped Nat
open scoped Real

/--
Suppose $a,b,c$ are the sides of a triangle. Prove that \[ a^2(b+c-a)+b^2(a+c-b)+c^2(a+b-c) \leq 3abc  \] -/
theorem imo_1964_p2 (a b c : ℝ) (h₀ : 0 < a ∧ 0 < b ∧ 0 < c) (h₁ : c < a + b) (h₂ : b < a + c)
    (h₃ : a < b + c) :
    a ^ 2 * (b + c - a) + b ^ 2 * (c + a - b) + c ^ 2 * (a + b - c) ≤ 3 * a * b * c := by
  have h₄ : 0 < b + c - a := by linarith
  have h₅ : 0 < c + a - b := by linarith
  have h₆ : 0 < a + b - c := by linarith
  have h₇ :
      0 ≤ (b + c - a) * ((c + a - b) - (a + b - c)) ^ 2 +
        (c + a - b) * ((a + b - c) - (b + c - a)) ^ 2 +
        (a + b - c) * ((b + c - a) - (c + a - b)) ^ 2 := by
    positivity
  have h₈ :
      8 * (3 * a * b * c -
        (a ^ 2 * (b + c - a) + b ^ 2 * (c + a - b) + c ^ 2 * (a + b - c))) =
        (b + c - a) * ((c + a - b) - (a + b - c)) ^ 2 +
        (c + a - b) * ((a + b - c) - (b + c - a)) ^ 2 +
        (a + b - c) * ((b + c - a) - (c + a - b)) ^ 2 := by
    ring
  linarith
