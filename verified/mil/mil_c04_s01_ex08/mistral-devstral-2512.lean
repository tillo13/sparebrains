import Mathlib

open Set

/-- Mathematics in Lean, Chapter 4 §1 (Sets), exercise 8. Avigad & Massot, Apache-2.0, commit dd6d752. -/
theorem mil_c04_s01_ex08 : { n | Nat.Prime n } ∩ { n | n > 2 } ⊆ { n | ¬Even n } := by
  intro n hn
  simp only [mem_inter_iff, mem_setOf_eq] at hn
  simp only [mem_setOf_eq]
  intro h
  have h1 : n % 2 = 0 := by
    obtain ⟨m, hm⟩ := h
    omega
  have h2 : n ≠ 2 := by
    omega
  have h3 : ¬ Nat.Prime n := by
    apply Nat.not_prime_of_dvd_of_lt (show 2 ∣ n by omega) (by omega) (by omega)
  tauto
