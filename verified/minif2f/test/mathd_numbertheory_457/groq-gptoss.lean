import Mathlib

open scoped Nat
open scoped Real

/-- What is the least positive integer $n$ such that $80325$ divides $n!$? -/
theorem mathd_numbertheory_457 : IsLeast {n : ℕ | 0 < n ∧ 80325 ∣ n !} 17 := by
  refine ⟨?_, ?_⟩
  · -- 17 belongs to the set
    have hpos : (0 : ℕ) < 17 := by decide
    have hdiv : 80325 ∣ 17 ! := by
      norm_num
    exact ⟨hpos, hdiv⟩
  · -- minimality
    intro m hm
    have h17dvd : (17 : ℕ) ∣ m ! :=
      Nat.dvd_trans (by norm_num : (17 : ℕ) ∣ 80325) hm.2
    have hprime : Nat.Prime 17 := by norm_num
    have hle : (17 : ℕ) ≤ m :=
      ((Nat.Prime.dvd_factorial hprime).1 h17dvd)
    exact hle
