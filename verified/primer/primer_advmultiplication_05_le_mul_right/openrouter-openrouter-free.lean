import Mathlib

/-- Natural Number Game (Lean 4), AdvMultiplication world, level 5: le_mul_right. Restated over Mathlib's ℕ. Source: https://github.com/leanprover-community/NNG4/blob/main/Game/Levels/AdvMultiplication/L05le_mul_right.lean, Apache-2.0. -/
theorem primer_advmultiplication_05_le_mul_right (a b : ℕ) (h : a * b ≠ 0) : a ≤ a * b := by
  have hb : b ≠ 0 := by
    intro hb
    apply h
    rw [hb]
    simp
  have ha : a ≠ 0 := by
    intro ha
    apply h
    rw [ha]
    simp
  -- Actually we only need one of them? Since a * b ≠ 0 implies both are nonzero. But to show a ≤ a * b, we can use `Nat.mul_le_mul_left`? Let's check: `Nat.mul_le_mul_left : a ≤ b → c * a ≤ c * b` for c ≥ 0? Actually `Nat.mul_le_mul_left` is for nonnegative? In ℕ all are nonnegative. So if we have `1 ≤ b`, then `a * 1 ≤ a * b` which simplifies to `a ≤ a * b`. So we can use:
  have h1leb : 1 ≤ b := Nat.one_le_iff_ne_zero.mpr hb
  calc
    a = a * 1 := by simp
    _ ≤ a * b := Nat.mul_le_mul_left a h1leb
