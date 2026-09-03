import Mathlib

/-- Natural Number Game (Lean 4), Tutorial world, level 5: Adding zero. Restated over Mathlib's ℕ. Source: https://github.com/leanprover-community/NNG4/blob/main/Game/Levels/Tutorial/L05add_zero.lean, Apache-2.0. -/
theorem primer_tutorial_05_add_zero (a b c : ℕ) : a + (b + 0) + (c + 0) = a + b + c := by
  -- First, use the associativity of addition to group terms
  rw [add_assoc, add_assoc]
  -- Then apply the addition of zero identity
  simp [add_zero]
  -- Finally, apply associativity again to reorder terms
  rw [add_assoc]
