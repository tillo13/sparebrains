import Mathlib

open scoped Nat
open scoped Real

/--
Solve the congruence $3n \equiv 2 \pmod{11}$, as a residue modulo 11.  (Give an answer between 0 and 10.) -/
theorem mathd_numbertheory_247 (n : ℕ) (h₀ : 3 * n % 2 = 11) : n % 11 = 8 := by
  have hlt : 3 * n % 2 < 2 := Nat.mod_lt _ (by decide)
  rw [h₀] at hlt
  have hfalse : ¬ 11 < 2 := by decide
  exact False.elim (hfalse hlt)
