import Mathlib

open scoped Nat
open scoped Real

/-- What is the value of
\[ (3x -{} 2)(4x +{} 1) -{} (3x -{} 2)4x +{} 1\]when $ x ={} 4$?

$ \textbf{(A)}\ 0 \qquad \textbf{(B)}\ 1 \qquad \textbf{(C)}\ 10 \qquad \textbf{(D)}\ 11 \qquad \textbf{(E)}\ 12$ -/
theorem amc12b_2002_p2 (x : ℤ) (h₀ : x = 4) :
    (3 * x - 2) * (4 * x + 1) - (3 * x - 2) * (4 * x) + 1 = 11 := by
  have h : x = 4 := h₀
  calc
    (3 * x - 2) * (4 * x + 1) - (3 * x - 2) * (4 * x) + 1
        = (3 * x - 2) * ((4 * x + 1) - (4 * x)) + 1 := by ring
    _ = (3 * x - 2) * 1 + 1 := by
      have : (4 * x + 1) - (4 * x) = 1 := by ring
      simpa [this]
    _ = 3 * x - 2 + 1 := by ring
    _ = 3 * x - 1 := by ring
    _ = 3 * 4 - 1 := by simpa [h]
    _ = 12 - 1 := by norm_num
    _ = 11 := by norm_num
