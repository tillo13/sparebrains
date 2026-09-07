import Mathlib

/-- Mathematics in Lean, Chapter 3 §2 (The Existential Quantifier), exercise 4. Avigad & Massot, Apache-2.0, commit dd6d752. -/
theorem mil_c03_s02_ex04 {a b c : ℕ} (divab : a ∣ b) (divbc : b ∣ c) : a ∣ c := by
  rcases divab with ⟨k₁, hk₁⟩
  rcases divbc with ⟨k₂, hk₂⟩
  refine ⟨k₁ * k₂, ?_⟩
  simpa [hk₁, hk₂, mul_comm, mul_left_comm, mul_assoc]
