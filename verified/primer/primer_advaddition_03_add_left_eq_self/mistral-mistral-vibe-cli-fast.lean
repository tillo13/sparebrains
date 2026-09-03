import Mathlib

/-- Natural Number Game (Lean 4), AdvAddition world, level 3: add_left_eq_self. Restated over Mathlib's ℕ. Source: https://github.com/leanprover-community/NNG4/blob/main/Game/Levels/AdvAddition/L03add_left_eq_self.lean, Apache-2.0. -/
theorem primer_advaddition_03_add_left_eq_self (x y : ℕ) : x + y = y → x = 0 := by
  intro h
  have h1 : x + y = y + x := by ac_rfl
  rw [h1] at h
  simp at h
  exact h
