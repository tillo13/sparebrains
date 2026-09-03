import Mathlib

/-- Natural Number Game (Lean 4), Power world, level 6: pow_add. Restated over Mathlib's ℕ. Source: https://github.com/leanprover-community/NNG4/blob/main/Game/Levels/Power/L06pow_add.lean, Apache-2.0. -/
theorem primer_power_06_pow_add (a m n : ℕ) : a ^ (m + n) = a ^ m * a ^ n := by
  have h : ∀ (m n : ℕ), a ^ (m + n) = a ^ m * a ^ n := by
    intro m n
    induction n with
    | zero =>
      simp
    | succ n ih =>
      rw [show m + (n + 1) = (m + n) + 1 by ring]
      rw [pow_succ]
      rw [ih]
      -- Now we have a ^ m * a ^ n * a
      -- We need to show this equals a ^ m * a ^ (n + 1)
      -- Since a ^ (n + 1) = a ^ n * a, we can use associativity and commutativity of multiplication.
      -- Actually, we can just use ring_nf to normalize both sides.
      <;> simp [pow_succ, mul_assoc, mul_comm, mul_left_comm] at *
      <;> ring_nf at *
      <;> linarith
  exact h m n
