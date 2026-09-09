import Mathlib

/-- Mathematics in Lean, Chapter 3 §2 (The Existential Quantifier), exercise 5. Avigad & Massot, Apache-2.0, commit dd6d752. -/
theorem mil_c03_s02_ex05 {a b c : ℕ} (divab : a ∣ b) (divac : a ∣ c) : a ∣ b + c := by
  rcases divab with ⟨k₁, hk₁⟩
  rcases divac with ⟨k₂, hk₂⟩
  refine ⟨k₁ + k₂, ?_⟩
  calc
    b + c = a * k₁ + a * k₂ := by simpa [hk₁, hk₂]
    _ = a * (k₁ + k₂) := by
      simpa [Nat.mul_add] using (Nat.mul_add a k₁ k₂).symm
