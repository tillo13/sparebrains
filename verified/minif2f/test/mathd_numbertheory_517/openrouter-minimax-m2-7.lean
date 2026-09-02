import Mathlib

open scoped Nat
open scoped Real

/-- Find the modulo 4 residue of $121 \cdot 122 \cdot 123$. -/
theorem mathd_numbertheory_517 : 121 * 122 * 123 % 4 = 2 := by
  rw [Nat.mul_mod, Nat.mul_mod]
  -- after first rewrite: ((121 % 4) * (122 % 4) * (123 % 4)) % 4? Actually two rewrites will give
  -- (121 % 4 * (122 * 123) % 4) % 4 = ((121 % 4) * ((122 % 4) * (123 % 4)) % 4) % 4? Not exactly.
