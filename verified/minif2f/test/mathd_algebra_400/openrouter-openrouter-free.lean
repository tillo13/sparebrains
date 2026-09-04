import Mathlib

open scoped Nat
open scoped Real

/-- Five plus $500\%$ of $10$ is the same as $110\%$ of what number? -/
theorem mathd_algebra_400 (x : ℝ) (h₀ : 5 + 500 / 100 * 10 = 110 / 100 * x) : x = 50 := by
  have h₁ : (5 : ℝ) + 500 / 100 * 10 = 55 := by
    norm_num
    <;>
    simp_all [div_eq_mul_inv]
    <;>
    norm_num
    <;>
    linarith
  
  have h₂ : (110 : ℝ) / 100 * x = 1.1 * x := by
    norm_num [div_eq_mul_inv]
    <;> ring_nf
    <;> norm_num
    <;> linarith
  
  have h₃ : (55 : ℝ) = 1.1 * x := by
    have h₃₁ : (5 : ℝ) + 500 / 100 * 10 = 110 / 100 * x := h₀
    have h₃₂ : (5 : ℝ) + 500 / 100 * 10 = 55 := h₁
    have h₃₃ : (110 : ℝ) / 100 * x = 1.1 * x := h₂
    linarith
  
  have h₄ : x = 50 := by
    have h₄₁ : (55 : ℝ) = 1.1 * x := h₃
    have h₄₂ : x = 50 := by
      -- Solve for x by dividing both sides by 1.1
      norm_num at h₄₁ ⊢
      <;>
      (try norm_num) <;>
      (try linarith) <;>
      (try ring_nf at h₄₁ ⊢) <;>
      (try nlinarith) <;>
      (try
        {
          apply mul_left_cancel₀ (show (1.1 : ℝ) ≠ 0 by norm_num)
          nlinarith
        }) <;>
      (try
        {
          field_simp at h₄₁ ⊢ <;>
          nlinarith
        })
      <;>
      nlinarith
    exact h₄₂
  
  rw [h₄]
  <;> norm_num
