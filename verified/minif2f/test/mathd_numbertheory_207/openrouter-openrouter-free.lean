import Mathlib

open scoped Nat
open scoped Real

/-- Convert $852_9$ to base 10. -/
theorem mathd_numbertheory_207 : 8 * 9 ^ 2 + 5 * 9 + 2 = 695 := by
  have h₁ : 8 * 9 ^ 2 + 5 * 9 + 2 = 695 := by
    norm_num
    <;> rfl
  
  apply h₁
