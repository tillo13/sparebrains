import Mathlib

open scoped Nat
open scoped Real

/--
Let $f(x) = |x - p| + |x - 15| + |x - p - 15|$, where $0 < p < 15$.  Determine the minimum value taken by $f(x)$ for $x$ in the interval $p \le x \le 15$. -/
theorem aime_1983_p2 (p : ℝ) (f : ℝ → ℝ) (h₀ : 0 < p ∧ p < 15)
    (h₂ : ∀ x, f x = abs (x - p) + abs (x - 15) + abs (x - p - 15)) : IsLeast (f '' Set.Icc p 15) 15 := by
  have hp : 0 < p := h₀.1
  have hp15 : p < 15 := h₀.2
  -- Show for any x in [p,15], f x = 30 - x
  have h_f_eq : ∀ x ∈ Set.Icc p 15, f x = 30 - x := by
    intro x hx
    rw [h₂ x]
    have hx_p : x - p ≥ 0 := by linarith [hx.1]
    have hx_15 : x - 15 ≤ 0 := by linarith [hx.2]
    have hx_p15 : x - p - 15 ≤ 0 := by linarith [hx.1, hx.2]
    simp [abs_of_nonneg hx_p, abs_of_nonpos hx_15, abs_of_nonpos hx_p15]
    ring
  -- Show for any x in [p,15], f x ≥ 15
  have h_min : ∀ x ∈ Set.Icc p 15, f x ≥ 15 := by
    intro x hx
    rw [h_f_eq x hx]
    linarith [hx.2]
  -- Show 15 is attained: at x=15
  have h_attain : f 15 = 15 := by
    rw [h_f_eq 15 (by constructor <;> linarith)]
    ring
  -- Now prove IsLeast
  constructor
  · -- 15 is in the image
    use 15
    constructor
    · constructor <;> linarith
    · exact h_attain
  · -- For any y in the image, 15 ≤ y
    intro y hy
    rcases hy with ⟨x, hx, rfl⟩
    exact h_min x hx
