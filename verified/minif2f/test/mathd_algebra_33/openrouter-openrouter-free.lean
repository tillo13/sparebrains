import Mathlib

open scoped Nat
open scoped Real

/--
If $2x = 5y$ and $7y = 10z$, what is the value of $\frac{z}{x}$ expressed as a common fraction? -/
theorem mathd_algebra_33 (x y z : ℝ) (h₀ : x ≠ 0) (h₁ : 2 * x = 5 * y) (h₂ : 7 * y = 10 * z) :
    z / x = 7 / 25 := by
  have h_y : y = (2 : ℝ) / 5 * x := by
    have h₃ : 5 * y = 2 * x := by linarith
    have h₄ : y = (2 : ℝ) / 5 * x := by
      -- Solve for y by dividing both sides by 5
      have h₅ : y = (2 * x) / 5 := by
        -- Use the fact that 5 * y = 2 * x to get y = (2 * x) / 5
        field_simp at h₃ ⊢
        <;> nlinarith
      -- Simplify (2 * x) / 5 to (2 / 5) * x
      calc
        y = (2 * x) / 5 := h₅
        _ = (2 : ℝ) / 5 * x := by ring
    exact h₄
  
  have h_z : z = (7 : ℝ) / 25 * x := by
    have h₃ : 10 * z = 7 * y := by linarith
    have h₄ : z = (7 : ℝ) / 10 * y := by
      -- Solve for z by dividing both sides by 10
      have h₅ : z = (7 * y) / 10 := by
        field_simp at h₃ ⊢
        <;> nlinarith
      -- Simplify (7 * y) / 10 to (7 / 10) * y
      calc
        z = (7 * y) / 10 := h₅
        _ = (7 : ℝ) / 10 * y := by ring
    -- Substitute y = (2 / 5) * x into z = (7 / 10) * y
    rw [h₄, h_y]
    -- Simplify the expression to get z = (7 / 25) * x
    <;> ring_nf
    <;> field_simp
    <;> ring_nf
    <;> norm_num
  
  have h_main : z / x = 7 / 25 := by
    rw [h_z]
    -- Simplify the expression (7 / 25 * x) / x to 7 / 25
    field_simp [h₀]
    <;> ring_nf
    <;> norm_num
  
  rw [h_main]
  <;> norm_num
