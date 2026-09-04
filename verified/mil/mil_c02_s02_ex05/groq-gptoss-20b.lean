import Mathlib

/-- Mathematics in Lean, Chapter 2 §2 (Proving Identities in Algebraic Structures), exercise 5. Avigad & Massot, Apache-2.0, commit dd6d752. -/
theorem mil_c02_s02_ex05 {R : Type*} [Ring R] {a b : R} (h : a + b = 0) : -a = b := by
  have hb : b = -a := by
    have : b + a = 0 := by simpa [add_comm] using h
    exact (eq_neg_iff_add_eq_zero).2 this
  simpa using hb.symm
