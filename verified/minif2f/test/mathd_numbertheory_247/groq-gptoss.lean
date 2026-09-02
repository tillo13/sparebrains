import Mathlib

open scoped Nat
open scoped Real

/--
Solve the congruence $3n \equiv 2 \pmod{11}$, as a residue modulo 11.  (Give an answer between 0 and 10.) -/
theorem mathd_numbertheory_247 (n : ℕ) (h₀ : 3 * n % 2 = 11) : n % 11 = 8 := by
  have hfalse : False := by
    have hlt : (3 * n) % 2 < 2 := Nat.mod_lt _ (by decide)
    have hlt11 : (11 : ℕ) < 2 := by
      simpa [h₀] using hlt
    exact (Nat.not_lt.mpr (Nat.le_of_lt (by decide : (2 : ℕ) < 11))) hlt11
  exact (False.elim hfalse)
