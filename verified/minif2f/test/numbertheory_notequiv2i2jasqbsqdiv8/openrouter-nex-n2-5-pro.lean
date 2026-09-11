import Mathlib

open scoped Nat
open scoped Real

theorem numbertheory_notequiv2i2jasqbsqdiv8 :
    ¬∀ a b : ℤ, (∃ i j, a = 2 * i ∧ b = 2 * j) ↔ ∃ k, a ^ 2 + b ^ 2 = 8 * k := by
  intro h
  have h20 := h 2 0
  have hleft : ∃ i j : ℤ, (2 : ℤ) = 2 * i ∧ (0 : ℤ) = 2 * j := by
    use 1, 0
    norm_num
  have hright := h20.mp hleft
  rcases hright with ⟨k, hk⟩
  norm_num at hk
  omega
