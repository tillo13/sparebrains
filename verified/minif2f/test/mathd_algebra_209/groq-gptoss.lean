import Mathlib

open scoped Nat
open scoped Real

/-- Suppose that $h(x)=f^{-1}(x)$. If $h(2)=10$, $h(10)=1$ and $h(1)=2$, what is $f(f(10))$? -/
theorem mathd_algebra_209 (σ : ℝ ≃ ℝ) (h₀ : σ.symm 2 = 10) (h₁ : σ.symm 10 = 1)
    (h₂ : σ.symm 1 = 2) : σ (σ 10) = 1 := by
  have h10 : σ 10 = 2 := by
    simpa [h₀] using σ.apply_symm_apply 2
  have h2 : σ 2 = 1 := by
    simpa [h₂] using σ.apply_symm_apply 1
  calc
    σ (σ 10) = σ 2 := by simpa [h10]
    _ = 1 := h2
