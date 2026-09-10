import Mathlib

open scoped Nat
open scoped Real

/-- What is the least positive integer $n$ such that $80325$ divides $n!$? -/
theorem mathd_numbertheory_457 : IsLeast {n : ℕ | 0 < n ∧ 80325 ∣ n !} 17 := by
  refine' ⟨⟨by norm_num, _⟩, _⟩
  · norm_num [Nat.factorial]
  · rintro n ⟨_, h⟩
    by_contra hnot
    have h17 : 17 ∣ n ! := dvd_trans (by norm_num) h
    rw [Nat.Prime.dvd_factorial (by decide)] at h17
    exact hnot h17
