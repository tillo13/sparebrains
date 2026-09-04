import Mathlib

/-- Mathematics in Lean, Chapter 2 §2 (Proving Identities in Algebraic Structures), exercise 1. Avigad & Massot, Apache-2.0, commit dd6d752. -/
theorem mil_c02_s02_ex01 {R : Type*} [Ring R] (a b : R) : a + b + -b = a := by
  -- Use the additive inverse property: b + -b = 0
  -- Then a + 0 = a by the additive identity property
  simp [add_zero, add_comm]
