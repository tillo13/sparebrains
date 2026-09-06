import Mathlib

open scoped Nat
open scoped Real

/--
If $a \star b = \dfrac{\left(\dfrac{1}{b} - \dfrac{1}{a}\right)}{(a - b)}$, express $3 \star 11$ as a common fraction. -/
theorem mathd_algebra_139 (s : ℝ → ℝ → ℝ)
    (h₀ : ∀ x ≠ 0, ∀ y ≠ 0, s x y = (1 / y - 1 / x) / (x - y)) :
    s 3 11 = 1 / 33 := by
  have h₁ : (3 : ℝ) ≠ 0 := by
    norm_num
    <;>
    simp_all [zero_eq]
    <;>
    norm_num
  
  have h₂ : (11 : ℝ) ≠ 0 := by
    norm_num
    <;>
    simp_all [zero_eq]
    <;>
    norm_num
  
  have h₃ : s 3 11 = (1 / (11 : ℝ) - 1 / (3 : ℝ)) / ((3 : ℝ) - (11 : ℝ)) := by
    have h₃₁ : s 3 11 = (1 / (11 : ℝ) - 1 / (3 : ℝ)) / ((3 : ℝ) - (11 : ℝ)) := by
      have h₃₂ := h₀ (3 : ℝ) h₁ (11 : ℝ) h₂
      norm_num at h₃₂ ⊢
      <;>
      (try ring_nf at h₃₂ ⊢) <;>
      (try norm_num at h₃₂ ⊢) <;>
      (try linarith) <;>
      (try simp_all) <;>
      (try field_simp at h₃₂ ⊢) <;>
      (try ring_nf at h₃₂ ⊢) <;>
      (try norm_num at h₃₂ ⊢) <;>
      (try linarith)
      <;>
      rw [h₃₂]
      <;>
      norm_num
    rw [h₃₁]
    <;>
    norm_num
  
  have h₄ : (1 / (11 : ℝ) - 1 / (3 : ℝ)) / ((3 : ℝ) - (11 : ℝ)) = 1 / 33 := by
    norm_num [div_eq_mul_inv]
    <;>
    field_simp
    <;>
    ring_nf
    <;>
    norm_num
  
  have h₅ : s 3 11 = 1 / 33 := by
    rw [h₃]
    rw [h₄]
    <;>
    norm_num
  
  rw [h₅]
  <;>
  norm_num
