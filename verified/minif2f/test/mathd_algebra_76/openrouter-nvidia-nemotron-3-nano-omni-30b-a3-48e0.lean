import Mathlib

open scoped Nat
open scoped Real

/-- For integers $n$, let \[f(n) = \left\{
\begin{array}{cl}
n^2 & \text{ if }n\text{ is odd}, \\
n^2 - 4n - 1 & \text{ if }n\text{ is even}.
\end{array}
\right.\]Find $f(f(f(f(f(4)))))$. -/
theorem mathd_algebra_76 (f : ℤ → ℤ) (h₀ : ∀ n, Odd n → f n = n ^ 2)
    (h₁ : ∀ n, Even n → f n = n ^ 2 - 4 * n - 1) : f 4 = -1 := by
  have h_even : Even (4 : ℤ) := by
    -- Prove that 4 is even by showing it is divisible by 2.
    apply Int.even_iff.mpr
    norm_num
    <;> simp [Int.emod_eq_of_lt]
    <;> norm_num
  
  have h_f4 : f 4 = (4 : ℤ) ^ 2 - 4 * (4 : ℤ) - 1 := by
    have h₂ : f 4 = (4 : ℤ) ^ 2 - 4 * (4 : ℤ) - 1 := by
      -- Use the given property for even numbers to compute f(4)
      have h₃ : Even (4 : ℤ) := h_even
      have h₄ : f 4 = (4 : ℤ) ^ 2 - 4 * (4 : ℤ) - 1 := by
        apply h₁
        exact h₃
      exact h₄
    exact h₂
  
  have h_calc : (4 : ℤ) ^ 2 - 4 * (4 : ℤ) - 1 = -1 := by
    norm_num
    <;> ring_nf at *
    <;> norm_num
    <;> linarith
  
  have h_main : f 4 = -1 := by
    rw [h_f4]
    rw [h_calc]
  
  exact h_main
