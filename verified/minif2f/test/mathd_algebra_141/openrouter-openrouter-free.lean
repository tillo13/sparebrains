import Mathlib

open scoped Nat
open scoped Real

/--
A rectangular patio has an area of $180$ square feet and a perimeter of $54$ feet. What is the length of the diagonal (in feet) squared? -/
theorem mathd_algebra_141 (a b : ℝ) (h₁ : a * b = 180) (h₂ : 2 * (a + b) = 54) :
    a ^ 2 + b ^ 2 = 369 := by
  have h_sum : a + b = 27 := by
    have h₃ : a + b = 27 := by
      linarith
    exact h₃
  
  have h_sum_sq : (a + b) ^ 2 = 729 := by
    rw [h_sum]
    <;> norm_num
  
  have h_expand : (a + b) ^ 2 = a ^ 2 + 2 * (a * b) + b ^ 2 := by
    have h₃ : (a + b) ^ 2 = a ^ 2 + 2 * (a * b) + b ^ 2 := by
      ring
    rw [h₃]
    <;>
    simp_all [mul_assoc]
    <;>
    ring_nf at *
    <;>
    nlinarith
  
  have h_subst : a ^ 2 + 2 * (a * b) + b ^ 2 = 729 := by
    linarith
  
  have h_ab : 2 * (a * b) = 360 := by
    have h₃ : a * b = 180 := h₁
    have h₄ : 2 * (a * b) = 360 := by
      calc
        2 * (a * b) = 2 * 180 := by rw [h₃]
        _ = 360 := by norm_num
    exact h₄
  
  have h_final : a ^ 2 + b ^ 2 = 369 := by
    have h₃ : a ^ 2 + 2 * (a * b) + b ^ 2 = 729 := h_subst
    have h₄ : 2 * (a * b) = 360 := h_ab
    have h₅ : a ^ 2 + b ^ 2 = 369 := by
      linarith
    exact h₅
  
  rw [h_final]
  <;> norm_num
