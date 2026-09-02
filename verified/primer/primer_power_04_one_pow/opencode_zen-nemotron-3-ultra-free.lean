import Mathlib

/-- Natural Number Game (Lean 4), Power world, level 4: one_pow. Restated over Mathlib's ℕ. Source: https://github.com/leanprover-community/NNG4/blob/main/Game/Levels/Power/L04one_pow.lean, Apache-2.0. -/
theorem primer_power_04_one_pow (m : ℕ) : (1 : ℕ) ^ m = 1 := by
  have h_base : (1 : ℕ) ^ 0 = 1 := by
    norm_num
    <;> rfl
  
  have h_inductive_step : ∀ (m : ℕ), (1 : ℕ) ^ m = 1 → (1 : ℕ) ^ (m + 1) = 1 := by
    intro m ih
    rw [pow_succ]
    rw [ih]
    <;> norm_num
  
  have h_main : (1 : ℕ) ^ m = 1 := by
    have h : ∀ m : ℕ, (1 : ℕ) ^ m = 1 := by
      intro m
      induction m with
      | zero => simp [h_base]
      | succ m ih =>
        apply h_inductive_step
        exact ih
    apply h
  
  apply h_main
