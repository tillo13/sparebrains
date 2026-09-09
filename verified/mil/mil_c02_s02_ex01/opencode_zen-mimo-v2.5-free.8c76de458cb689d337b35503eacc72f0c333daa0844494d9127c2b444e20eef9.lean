import Mathlib

/-- Mathematics in Lean, Chapter 2 §2 (Proving Identities in Algebraic Structures), exercise 1. Avigad & Massot, Apache-2.0, commit dd6d752. -/
theorem mil_c02_s02_ex01 {R : Type*} [Ring R] (a b : R) : a + b + -b = a := by
  calc
    a + b + -b = a + (b + -b) := by rw [add_assoc]
    _ = a + 0 := by rw [add_neg_cancel]
    _ = a := by rw [add_zero]
