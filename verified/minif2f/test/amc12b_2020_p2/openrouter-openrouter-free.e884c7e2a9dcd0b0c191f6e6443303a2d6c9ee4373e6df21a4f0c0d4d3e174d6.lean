import Mathlib

open scoped Nat
open scoped Real

/-- What is the value of the following expression?
$$\frac{100^2-7^2}{70^2-11^2} \cdot \frac{(70-11)(70+11)}{(100-7)(100+7)}$$
$\textbf{(A) } 1 \qquad \textbf{(B) } \frac{9951}{9950} \qquad \textbf{(C) } \frac{4780}{4779} \qquad \textbf{(D) } \frac{108}{107} \qquad \textbf{(E) } \frac{81}{80} $ -/
theorem amc12b_2020_p2 :
    (100 ^ 2 - 7 ^ 2 : ℝ) / (70 ^ 2 - 11 ^ 2) * ((70 - 11) * (70 + 11) / ((100 - 7) * (100 + 7))) =
      1 := by
  have h₁ : (100 : ℝ) ^ 2 - 7 ^ 2 = (100 - 7) * (100 + 7) := by
    norm_num [pow_two]
    <;> ring_nf
    <;> norm_num
    <;> linarith
  
  have h₂ : (70 : ℝ) ^ 2 - 11 ^ 2 = (70 - 11) * (70 + 11) := by
    norm_num [pow_two]
    <;> ring_nf
    <;> norm_num
    <;> linarith
  
  have h₃ : (100 ^ 2 - 7 ^ 2 : ℝ) / (70 ^ 2 - 11 ^ 2) * ((70 - 11) * (70 + 11) / ((100 - 7) * (100 + 7))) = 1 := by
    have h₄ : (100 : ℝ) ^ 2 - 7 ^ 2 = (100 - 7) * (100 + 7) := by exact_mod_cast h₁
    have h₅ : (70 : ℝ) ^ 2 - 11 ^ 2 = (70 - 11) * (70 + 11) := by exact_mod_cast h₂
    have h₆ : (100 ^ 2 - 7 ^ 2 : ℝ) = (100 - 7) * (100 + 7) := by
      norm_num [pow_two] at h₄ ⊢
      <;> ring_nf at h₄ ⊢ <;> norm_num at h₄ ⊢ <;> linarith
    have h₇ : (70 ^ 2 - 11 ^ 2 : ℝ) = (70 - 11) * (70 + 11) := by
      norm_num [pow_two] at h₅ ⊢
      <;> ring_nf at h₅ ⊢ <;> norm_num at h₅ ⊢ <;> linarith
    calc
      (100 ^ 2 - 7 ^ 2 : ℝ) / (70 ^ 2 - 11 ^ 2) * ((70 - 11) * (70 + 11) / ((100 - 7) * (100 + 7))) =
          ((100 - 7) * (100 + 7) : ℝ) / ((70 - 11) * (70 + 11)) * ((70 - 11) * (70 + 11) / ((100 - 7) * (100 + 7))) := by
        rw [h₆, h₇]
        <;> ring_nf
      _ = 1 := by
        have h₈ : (100 - 7 : ℝ) ≠ 0 := by norm_num
        have h₉ : (100 + 7 : ℝ) ≠ 0 := by norm_num
        have h₁₀ : (70 - 11 : ℝ) ≠ 0 := by norm_num
        have h₁₁ : (70 + 11 : ℝ) ≠ 0 := by norm_num
        field_simp [h₈, h₉, h₁₀, h₁₁]
        <;> ring_nf
        <;> norm_num
        <;> linarith
  
  exact h₃
