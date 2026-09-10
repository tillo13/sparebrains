import Mathlib

open scoped Nat
open scoped Real

/--
Ms. Blackwell gives an exam to two classes. The mean of the scores of the students in the morning class is $84$, and the afternoon class’s mean score is $70$. The ratio of the number of students in the morning class to the number of students in the afternoon class is $\frac{3}{4}$. What is the mean of the scores of all the students?

$\textbf{(A) }74 \qquad \textbf{(B) }75 \qquad \textbf{(C) }76 \qquad \textbf{(D) }77 \qquad \textbf{(E) }78$ -/
theorem amc12b_2021_p4 (m a : ℕ) (h₀ : 0 < m ∧ 0 < a) (h₁ : ↑m / ↑a = (3 : ℝ) / 4) :
    (84 * ↑m + 70 * ↑a) / (↑m + ↑a) = (76 : ℝ) := by
  -- `a` is nonzero
  have ha0 : (a : ℝ) ≠ 0 := by
    have : (0 : ℝ) < (a : ℝ) := by
      exact_mod_cast h₀.2
    exact ne_of_gt this
  -- rewrite `m` using the given ratio
  have hm_eq : (m : ℝ) = (3 / 4) * (a : ℝ) := by
    have h := h₁
    field_simp [ha0] at h
    -- now `h : (m : ℝ) * 4 = (a : ℝ) * 3`
    have : (m : ℝ) = ((a : ℝ) * 3) / 4 :=
      (eq_div_iff_mul_eq (by norm_num : (4 : ℝ) ≠ 0)).mpr
        (by
          simpa [mul_comm, mul_left_comm, mul_assoc] using h)
    simpa [div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc] using this
  calc
    (84 * (m : ℝ) + 70 * (a : ℝ)) / ((m : ℝ) + (a : ℝ))
        = (84 * ((3 / 4) * (a : ℝ)) + 70 * (a : ℝ)) /
            (((3 / 4) * (a : ℝ)) + (a : ℝ)) := by
          simpa [hm_eq]
    _ = (a : ℝ) * (84 * (3 / 4) + 70) /
            ((a : ℝ) * ((3 / 4) + 1)) := by
          have hnum :
              84 * ((3 / 4) * (a : ℝ)) + 70 * (a : ℝ) =
                (a : ℝ) * (84 * (3 / 4) + 70) := by
            ring
          have hden :
              ((3 / 4) * (a : ℝ) + (a : ℝ)) =
                (a : ℝ) * ((3 / 4) + 1) := by
            ring
          simpa [hnum, hden]
    _ = (84 * (3 / 4) + 70) / ((3 / 4) + 1) := by
          field_simp [ha0]
    _ = (84 * (3 / 4) + 70) / (7 / 4) := by
          norm_num
    _ = 76 := by
          norm_num
