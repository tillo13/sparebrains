import Mathlib

/-- Mathematics in Lean, Chapter 3 §2 (The Existential Quantifier), exercise 5. Avigad & Massot, Apache-2.0, commit dd6d752. -/
theorem mil_c03_s02_ex05 {a b c : ℕ} (divab : a ∣ b) (divac : a ∣ c) : a ∣ b + c := by
  obtain ⟨m, h1⟩ := divab
  obtain ⟨n, h2⟩ := divac
  refine ⟨m + n, ?_⟩
  rw [h1, h2]
  ring
