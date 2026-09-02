import Mathlib

/-- Natural Number Game (Lean 4), Power world, level 2: zero_pow_succ. Restated over Mathlib's ℕ. Source: https://github.com/leanprover-community/NNG4/blob/main/Game/Levels/Power/L02zero_pow_succ.lean, Apache-2.0. -/
theorem primer_power_02_zero_pow_succ (m : ℕ) : (0 : ℕ) ^ (Nat.succ m) = 0 := by
  have h_main : (0 : ℕ) ^ (Nat.succ m) = 0 := by
    have h : Nat.succ m ≠ 0 := by
      intro h₁
      -- Prove that the successor of any natural number is not zero.
      simp [Nat.succ_ne_zero] at h₁
    -- Use the property of zero powers: 0^n = 0 for n ≠ 0.
    simp [Nat.zero_pow, h]
    <;> aesop
  
  rw [h_main]
  <;> simp
