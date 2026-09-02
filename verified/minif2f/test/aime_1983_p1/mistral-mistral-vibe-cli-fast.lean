import Mathlib

open scoped Nat
open scoped Real

/--
Let $x$, $y$, and $z$ all exceed 1 and let $w$ be a positive number such that \[\log_x w = 24,\quad \log_y w = 40 \quad\text{and}\quad \log_{xyz} w = 12.\]  Find $\log_z w$. -/
theorem aime_1983_p1 (x y z w : ℕ) (ht : 1 < x ∧ 1 < y ∧ 1 < z) (hw : 0 ≤ w)
    (h0 : Real.log w / Real.log x = 24) (h1 : Real.log w / Real.log y = 40)
    (h2 : Real.log w / Real.log (x * y * z) = 12) : Real.log w / Real.log z = 60 := by
  have hx : (x : ℝ) > 1 := by exact_mod_cast ht.1
  have hy : (y : ℝ) > 1 := by exact_mod_cast ht.2.1
  have hz : (z : ℝ) > 1 := by exact_mod_cast ht.2.2
  have hw' : (w : ℝ) ≥ 0 := by exact_mod_cast hw
  have h3 : Real.log (x * y * z : ℝ) = Real.log (x : ℝ) + Real.log (y : ℝ) + Real.log (z : ℝ) := by
    rw [Real.log_mul (by positivity) (by positivity), Real.log_mul (by positivity) (by positivity)]
    all_goals ring_nf
  have h4 : Real.log w = 24 * Real.log (x : ℝ) := by
    have h5 : Real.log (x : ℝ) ≠ 0 := by
      have h6 : Real.log (x : ℝ) > 0 := by
        apply Real.log_pos
        linarith
      linarith
    field_simp [h5] at h0 ⊢
    linarith
  have h7 : Real.log w = 40 * Real.log (y : ℝ) := by
    have h8 : Real.log (y : ℝ) ≠ 0 := by
      have h9 : Real.log (y : ℝ) > 0 := by
        apply Real.log_pos
        linarith
      linarith
    field_simp [h8] at h1 ⊢
    linarith
  have h10 : Real.log w = 12 * (Real.log (x : ℝ) + Real.log (y : ℝ) + Real.log (z : ℝ)) := by
    have h11 : Real.log (x * y * z : ℝ) ≠ 0 := by
      have h12 : Real.log (x * y * z : ℝ) > 0 := by
        have h13 : (x * y * z : ℝ) > 1 := by
          have h14 : (x : ℝ) > 1 := hx
          have h15 : (y : ℝ) > 1 := hy
          have h16 : (z : ℝ) > 1 := hz
          have h17 : (x * y : ℝ) > 1 := by nlinarith
          nlinarith
        apply Real.log_pos
        linarith
      linarith
    field_simp [h11, h3] at h2 ⊢
    linarith
  have h18 : Real.log (z : ℝ) = (Real.log w) / 60 := by
    nlinarith [h4, h7, h10]
  have h19 : Real.log (z : ℝ) ≠ 0 := by
    have h20 : Real.log (z : ℝ) > 0 := by
      apply Real.log_pos
      linarith
    linarith
  field_simp [h19] at h18 ⊢
  linarith [h18, h4]
