import Mathlib

open scoped Nat
open scoped Real

/--
Ms. Blackwell gives an exam to two classes. The mean of the scores of the students in the morning class is $84$, and the afternoon class’s mean score is $70$. The ratio of the number of students in the morning class to the number of students in the afternoon class is $\frac{3}{4}$. What is the mean of the scores of all the students?

$\textbf{(A) }74 \qquad \textbf{(B) }75 \qquad \textbf{(C) }76 \qquad \textbf{(D) }77 \qquad \textbf{(E) }78$ -/
theorem amc12b_2021_p4 (m a : ℕ) (h₀ : 0 < m ∧ 0 < a) (h₁ : ↑m / ↑a = (3 : ℝ) / 4) :
    (84 * ↑m + 70 * ↑a) / (↑m + ↑a) = (76 : ℝ) := by
  have hm : 0 < m := h₀.left
  have ha : 0 < a := h₀.right
  have ha_ne : (a : ℝ) ≠ 0 := by exact_mod_cast ha.ne'
  field_simp [ha_ne] at h₁
  have h_sum_pos : (0 : ℝ) < (m : ℝ) + (a : ℝ) := by
    exact_mod_cast add_pos hm ha
  have h_denom : (m : ℝ) + (a : ℝ) ≠ 0 := ne_of_gt h_sum_pos
  field_simp [h_denom] at ⊢
  linarith [h₁]
