import Mathlib

open scoped Nat
open scoped Real

/--
For each plumbing repair job, Mr. Wrench charges $N$ dollars for coming out to the house plus $x$ dollars per hour that he works at the house. He charged $\$97$ for a one-hour repair job and $\$265$ for a five-hour repair job. What is his charge for a two-hour repair job? -/
theorem mathd_algebra_160 (n x : ℝ) (h₀ : n + x = 97) (h₁ : n + 5 * x = 265) : n + 2 * x = 139 := by
  have h₂ : 4 * x = 168 := by
    calc
      4 * x = (n + 5 * x) - (n + x) := by ring
      _ = 265 - 97 := by rw [h₁, h₀]
      _ = 168 := by norm_num
  have h₃ : x = 42 := by linarith
  have h₄ : n + 2 * x = 139 := by
    calc
      n + 2 * x = (n + x) + x := by ring
      _ = 97 + x := by rw [h₀]
      _ = 97 + 42 := by rw [h₃]
      _ = 139 := by norm_num
  exact h₄
