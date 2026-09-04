import Mathlib

open scoped Nat
open scoped Real

/-- Assuming $x\ne0$, simplify $\frac{12}{x \cdot x} \cdot \frac{x^4}{14x}\cdot \frac{35}{3x}$. -/
theorem mathd_algebra_441 (x : ℝ) (h₀ : x ≠ 0) :
    12 / (x * x) * (x ^ 4 / (14 * x)) * (35 / (3 * x)) = 10 := by
  have h₁ : 12 / (x * x) * (x ^ 4 / (14 * x)) * (35 / (3 * x)) = 10 := by
    have h₂ : x * x ≠ 0 := by
      apply mul_ne_zero
      · exact h₀
      · exact h₀
    have h₃ : 14 * x ≠ 0 := by
      apply mul_ne_zero
      · norm_num
      · exact h₀
    have h₄ : 3 * x ≠ 0 := by
      apply mul_ne_zero
      · norm_num
      · exact h₀
    have h₅ : x ^ 4 ≠ 0 := by
      exact pow_ne_zero 4 h₀
    -- Simplify the expression step by step
    have h₆ : 12 / (x * x) * (x ^ 4 / (14 * x)) * (35 / (3 * x)) = (12 * x ^ 4 * 35) / (x * x * (14 * x) * (3 * x)) := by
      field_simp [h₂, h₃, h₄]
      <;> ring_nf
      <;> field_simp [h₂, h₃, h₄]
      <;> ring_nf
      <;> nlinarith
    rw [h₆]
    have h₇ : (12 * x ^ 4 * 35 : ℝ) / (x * x * (14 * x) * (3 * x)) = 10 := by
      have h₈ : x * x * (14 * x) * (3 * x) = 42 * x ^ 4 := by
        ring_nf
        <;> field_simp [h₀]
        <;> ring_nf
        <;> nlinarith
      rw [h₈]
      have h₉ : (12 * x ^ 4 * 35 : ℝ) = 420 * x ^ 4 := by
        ring_nf
        <;> field_simp [h₀]
        <;> ring_nf
        <;> nlinarith
      rw [h₉]
      have h₁₀ : (420 * x ^ 4 : ℝ) / (42 * x ^ 4) = 10 := by
        have h₁₁ : (42 : ℝ) ≠ 0 := by norm_num
        have h₁₂ : (x ^ 4 : ℝ) ≠ 0 := by exact_mod_cast h₅
        field_simp [h₁₁, h₁₂]
        <;> ring_nf
        <;> norm_num
        <;> field_simp [h₀]
        <;> ring_nf
        <;> nlinarith
      rw [h₁₀]
    rw [h₇]
  rw [h₁]
  <;> norm_num
