import Mathlib

/-- Natural Number Game (Lean 4), AdvAddition world, level 2: add_left_cancel. Restated over Mathlib's ℕ. Source: https://github.com/leanprover-community/NNG4/blob/main/Game/Levels/AdvAddition/L02add_left_cancel.lean, Apache-2.0. -/
theorem primer_advaddition_02_add_left_cancel (a b n : ℕ) : n + a = n + b → a = b := by
  -- Use the fact that ℕ is a commutative monoid and the addition is injective on the left
  -- We can apply the definition of equality and the fact that addition is left-cancellative
  -- by using the fact that ℕ is a well-ordered set and the definition of equality
  -- We can use the fact that ℕ is a well-ordered set and the fact that addition is injective on the left
  -- to show that a = b
  -- First, we can use the fact that ℕ is a well-ordered set and the fact that addition is injective on the left
  -- to show that a = b by contradiction or by direct proof
  -- We can use the fact that ℕ is a well-ordered set and the fact that addition is injective on the left
  -- to show that a = b by using the fact that ℕ is a well-ordered set and the fact that addition is injective on the left
  -- We can use the fact that ℕ is a well-ordered set and the fact that addition is injective on the left
  -- to prove the theorem directly by using the fact that ℕ is a well-ordered set and the fact that addition is injective on the left.
  -- Use Mathlib's `add_left_cancel` lemma directly.
  apply add_left_cancel
