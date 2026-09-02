import Mathlib

/-- Natural Number Game (Lean 4), Multiplication world, level 8: add_mul. Restated over Mathlib's ℕ. Source: https://github.com/leanprover-community/NNG4/blob/main/Game/Levels/Multiplication/L08add_mul.lean, Apache-2.0. -/
theorem primer_multiplication_08_add_mul (a b c : ℕ) : (a + b) * c = a * c + b * c := by
  have h_main : (a + b) * c = a * c + b * c := by
    induction c with
    | zero =>
      -- Base case: when c = 0, both sides are 0.
      simp
    | succ c ih =>
      -- Inductive step: assume the statement holds for c, prove for c + 1.
      simp_all [Nat.mul_succ, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]
      <;> ring_nf at *
      <;> omega
  
  rw [h_main]
  <;> simp_all
