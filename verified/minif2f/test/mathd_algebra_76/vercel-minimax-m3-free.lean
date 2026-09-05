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
  have h₂ : Even (4 : ℤ) := ⟨2, by norm_num⟩
  have h₃ : Odd (-1 : ℤ) := ⟨-1, by ring⟩
  simp only [show (4 : ℤ) = 2 * 2 by norm_num] at h₂
  rw [h₁ 4 h₂]
  norm_num
