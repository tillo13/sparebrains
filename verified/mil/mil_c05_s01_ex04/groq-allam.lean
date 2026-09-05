import Mathlib

/-- Mathematics in Lean, Chapter 5 §1 (Irrational Roots), exercise 4. Avigad & Massot, Apache-2.0, commit dd6d752. -/
theorem mil_c05_s01_ex04 {m n : ℕ} (mnez : m ≠ 0) (nnez : n ≠ 0) (p : ℕ) :
    (m * n).factorization p = m.factorization p + n.factorization p := by
  -- The `Nat.factorization_mul` lemma states that the factorization of a product `m * n`
  -- is the sum of the factorizations of `m` and `n` as functions `ℕ → ℕ`.
  -- That is, `(m * n).factorization = m.factorization + n.factorization`.
  -- Applying this equality to `p` gives the desired result.
  rw [Nat.factorization_mul mnez nnez]
  -- The goal is now `(m.factorization + n.factorization) p = m.factorization p + n.factorization p`.
  -- This is true by the definition of function addition.
  rfl
