import Mathlib

open scoped Nat
open scoped Real

/-- What is the value of $$\frac{\log_2 80}{\log_{40}2}-\frac{\log_2 160}{\log_{20}2}?$$

$\textbf{(A) }0 \qquad \textbf{(B) }1 \qquad \textbf{(C) }\frac54 \qquad \textbf{(D) }2 \qquad \textbf{(E) }\log_2 5$ -/
theorem amc12b_2021_p9 :
    Real.log 80 / Real.log 2 / (Real.log 2 / Real.log 40) -
        Real.log 160 / Real.log 2 / (Real.log 2 / Real.log 20) =
      2 := by
  have hlog2 : Real.log 2 ≠ 0 := by positivity
  have hlog5 : Real.log 5 ≠ 0 := by positivity
  have hlog40 : Real.log 40 ≠ 0 := by positivity
  have hlog20 : Real.log 20 ≠ 0 := by positivity
  have hlog80 : Real.log 80 ≠ 0 := by positivity
  have hlog160 : Real.log 160 ≠ 0 := by positivity
  calc
    Real.log 80 / Real.log 2 / (Real.log 2 / Real.log 40) -
        Real.log 160 / Real.log 2 / (Real.log 2 / Real.log 20)
    = (Real.log 80 * Real.log 40) / (Real.log 2)^2 -
        (Real.log 160 * Real.log 20) / (Real.log 2)^2 := by
      field_simp [hlog2, hlog40, hlog20]
    _ = ((Real.log 80 * Real.log 40) - (Real.log 160 * Real.log 20)) / (Real.log 2)^2 := by
      ring
    _ = ((Real.log (2^4 * 5) * Real.log (2^3 * 5)) - (Real.log (2^5 * 5) * Real.log (2^2 * 5))) / (Real.log 2)^2 := by
      norm_num [Real.log_mul, Real.log_pow]
    _ = (((4 * Real.log 2 + Real.log 5) * (3 * Real.log 2 + Real.log 5)) -
        ((5 * Real.log 2 + Real.log 5) * (2 * Real.log 2 + Real.log 5))) / (Real.log 2)^2 := by
      simp [Real.log_mul, Real.log_pow]
    _ = (2 * Real.log 2^2) / (Real.log 2)^2 := by
      ring
    _ = 2 := by
      field_simp [hlog2]
