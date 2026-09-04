import Mathlib

open Function

/-- Mathematics in Lean, Chapter 3 §1 (Implication and the Universal Quantifier), exercise 16. Avigad & Massot, Apache-2.0, commit dd6d752. -/
theorem mil_c03_s01_ex16 {c : ℝ} (h : c ≠ 0) : Injective fun x ↦ c * x := by
  -- To prove that a function `f` is injective, we need to show that for any `x₁` and `x₂`,
  -- if `f x₁ = f x₂`, then `x₁ = x₂`.
  intro x₁ x₂
  intro h_eq -- This assumption is `c * x₁ = c * x₂`
  -- We are given the hypothesis `h : c ≠ 0`.
  -- Since `c` is a non-zero real number, we can cancel `c` from both sides of the equation `c * x₁ = c * x₂`.
  -- The `mul_left_cancel₀` lemma from Mathlib is suitable for this.
  -- It states: `mul_left_cancel₀ {α : Type*} [CommSemiring α] {a b c : α} (ha : a ≠ 0) : a * b = a * c → b = c`
  -- Here, `α` is `ℝ`, `a` is `c`, `b` is `x₁`, `c` is `x₂`.
  -- `ha` is our hypothesis `h : c ≠ 0`.
  -- The implication `a * b = a * c → b = c` is applied to `h_eq`.
  apply (mul_left_cancel₀ h) h_eq
