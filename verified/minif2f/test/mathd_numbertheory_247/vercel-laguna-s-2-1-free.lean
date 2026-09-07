import Mathlib

open scoped Nat
open scoped Real

/--
Solve the congruence $3n \equiv 2 \pmod{11}$, as a residue modulo 11.  (Give an answer between 0 and 10.) -/
theorem mathd_numbertheory_247 (n : ℕ) (h₀ : 3 * n % 2 = 11) : n % 11 = 8 := by
  -- The hypothesis as stated is unusual; we work with it directly.
  -- From h₀: 3 * n % 2 = 11. But 3 * n % 2 is either 0 or 1, so this is impossible
  -- unless we interpret it differently. We proceed formally.
  have h₁ : 3 * n % 2 = 11 := h₀
  -- Since 3 * n % 2 ∈ {0, 1}, this hypothesis is contradictory.
  -- From a false premise, anything follows.
  exfalso
  -- 3 * n % 2 is at most 1, but equals 11, contradiction.
  have h₂ : 3 * n % 2 ≤ 1 := by
    have : 3 * n % 2 ≤ 3 * n % 2 := by rfl
    -- Use the fact that for any natural a, a % 2 ≤ 1
    have h₃ : ∀ a : ℕ, a % 2 ≤ 1 := by
      intro a
      have : a % 2 < 2 := Nat.mod_lt a (by decide)
      omega
    exact h₃ (3 * n)
  linarith
