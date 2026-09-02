import Mathlib

open scoped Nat
open scoped Real

/--
For how many positive integers $ m$ does there exist at least one positive integer $ n$ such that $ m\cdot n \le m +{} n$?

$ \textbf{(A)}\ 4 \qquad \textbf{(B)}\ 6 \qquad \textbf{(C)}\ 9 \qquad \textbf{(D)}\ 12 \qquad \textbf{(E)}$ infinitely many -/
theorem amc12a_2002_p6 (n : ℕ) (h₀ : 0 < n) : ∃ m, m > n ∧ ∃ p, m * p ≤ m + p := by
  have h_main : ∃ (m : ℕ), m > n ∧ ∃ (p : ℕ), m * p ≤ m + p := by
    use n + 1
    constructor
    · -- Prove that n + 1 > n
      omega
    · -- Find p such that (n + 1) * p ≤ (n + 1) + p
      use 1
      -- Verify that (n + 1) * 1 ≤ (n + 1) + 1
      <;> simp [mul_comm, mul_assoc, mul_left_comm]
      <;> ring_nf at *
      <;> omega
  
  exact h_main
