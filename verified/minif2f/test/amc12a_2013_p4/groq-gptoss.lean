import Mathlib

open scoped Nat
open scoped Real

/-- What is the value of \[\frac{2^{2014}+2^{2012}}{2^{2014}-2^{2012}}?\]

$ \textbf{(A)}\ -1\qquad\textbf{(B)}\ 1\qquad\textbf{(C)}\ \frac{5}{3}\qquad\textbf{(D)}\ 2013\qquad\textbf{(E)}\ 2^{4024} $ -/
theorem amc12a_2013_p4 : (2 ^ 2014 + 2 ^ 2012) / (2 ^ 2014 - 2 ^ 2012) = (5 : ℝ) / 3 := by
  have hpow : (2 : ℝ) ^ 2014 = (2 : ℝ) ^ 2012 * (2 : ℝ) ^ 2 := by
    simpa using (pow_add (2 : ℝ) 2012 2)
  have hnum : 2 ^ 2014 + 2 ^ 2012 = (2 : ℝ) ^ 2012 * ((2 : ℝ) ^ 2 + 1) := by
    calc
      2 ^ 2014 + 2 ^ 2012
          = (2 : ℝ) ^ 2012 * (2 : ℝ) ^ 2 + 2 ^ 2012 := by
            simpa [hpow]
      _ = (2 : ℝ) ^ 2012 * ((2 : ℝ) ^ 2 + 1) := by ring
  have hden : 2 ^ 2014 - 2 ^ 2012 = (2 : ℝ) ^ 2012 * ((2 : ℝ) ^ 2 - 1) := by
    calc
      2 ^ 2014 - 2 ^ 2012
          = (2 : ℝ) ^ 2012 * (2 : ℝ) ^ 2 - 2 ^ 2012 := by
            simpa [hpow]
      _ = (2 : ℝ) ^ 2012 * ((2 : ℝ) ^ 2 - 1) := by ring
  have hne : (2 : ℝ) ^ 2012 ≠ 0 := by
    have h2 : (2 : ℝ) ≠ 0 := by norm_num
    exact pow_ne_zero _ h2
  calc
    (2 ^ 2014 + 2 ^ 2012) / (2 ^ 2014 - 2 ^ 2012)
        = ((2 : ℝ) ^ 2012 * ((2 : ℝ) ^ 2 + 1)) /
          ((2 : ℝ) ^ 2012 * ((2 : ℝ) ^ 2 - 1)) := by
            simpa [hnum, hden]
    _ = ((2 : ℝ) ^ 2 + 1) / ((2 : ℝ) ^ 2 - 1) := by
            field_simp [hne]
    _ = (5 : ℝ) / 3 := by
            norm_num
