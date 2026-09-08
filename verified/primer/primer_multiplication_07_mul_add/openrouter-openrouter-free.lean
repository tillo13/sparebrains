import Mathlib

/-- Natural Number Game (Lean 4), Multiplication world, level 7: mul_add. Restated over Mathlib's ℕ. Source: https://github.com/leanprover-community/NNG4/blob/main/Game/Levels/Multiplication/L07mul_add.lean, Apache-2.0. -/
theorem primer_multiplication_07_mul_add (a b c : ℕ) : a * (b + c) = a * b + a * c := by
  have h_main : a * (b + c) = a * b + a * c := by
    induction a with
    | zero => simp
    | succ a ih =>
      simp [Nat.succ_mul, ih, add_assoc, add_comm, add_left_comm]
      <;>
      (try ring_nf at *) <;>
      (try omega) <;>
      (try simp_all [add_assoc, add_comm, add_left_comm]) <;>
      (try linarith) <;>
      (try nlinarith)
      <;>
      (try
        {
          abel
        })
      <;>
      (try
        {
          ring_nf at *
          <;> omega
        })
  
  rw [h_main]
  <;> rfl
