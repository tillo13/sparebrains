import Mathlib

/-- Mathematics in Lean, Chapter 3 §2 (The Existential Quantifier), exercise 5. Avigad & Massot, Apache-2.0, commit dd6d752. -/
theorem mil_c03_s02_ex05 {a b c : ℕ} (divab : a ∣ b) (divac : a ∣ c) : a ∣ b + c := by
  rcases divab with ⟨k1, hk1⟩
  rcases divac with ⟨k2, hk2⟩
  use k1 + k2
  rw [hk1, hk2]
  ring
