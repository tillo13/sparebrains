import Mathlib

open Set

/-- Mathematics in Lean, Chapter 4 §1 (Sets), exercise 8. Avigad & Massot, Apache-2.0, commit dd6d752. -/
theorem mil_c04_s01_ex08 : { n | Nat.Prime n } ∩ { n | n > 2 } ⊆ { n | ¬Even n } := by
  intro n hn
  simp only [mem_setOf_eq, mem_inter_iff] at hn
  obtain ⟨h_prime, h_gt⟩ := hn
  simp only [mem_setOf_eq]
  by_contra h_even
  have h_two : 2 ∣ n := by
    obtain ⟨k, hk⟩ := h_even
    use k
    linarith
  have h_ne : n ≠ 2 := by
    omega
  have h_not_prime : ¬Nat.Prime n := by
    apply Nat.not_prime_of_dvd_of_lt (show 2 ∣ n by assumption) (by omega) (by omega)
  contradiction
