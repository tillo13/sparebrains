import Mathlib

open scoped Nat
open scoped Real

/--
A positive integer $X$ is 2 more than a multiple of 3. Its units digit is the same as the units digit of a number that is 4 more than a multiple of 5. What is the smallest possible value of $X$? -/
theorem mathd_numbertheory_559 :
    IsLeast {x : ℕ | 0 < x ∧ x % 3 = 2 ∧ ∃ y, y % 5 = 4 ∧ x % 10 = y % 10} 14 := by
  constructor
  · exact ⟨by norm_num, by norm_num, ⟨4, by norm_num, by norm_num⟩⟩
  · intro x hx
    rcases hx with ⟨h1,h2,y,h3,h4⟩
    have h5 : x % 10 = 4 ∨ x % 10 = 9 := by
      have h6 : (x % 10) % 5 = 4 := by
        rw [h4]
        omega
      omega
    cases h5 with
    | inl h5 => omega
    | inr h5 => omega
