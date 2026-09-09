import Mathlib

open scoped Nat
open scoped Real

theorem numbertheory_notequiv2i2jasqbsqdiv8 :
    ¬∀ a b : ℤ, (∃ i j, a = 2 * i ∧ b = 2 * j) ↔ ∃ k, a ^ 2 + b ^ 2 = 8 * k := by
  intro h
  have h2 : ((∃ i j : ℤ, 2 = 2 * i ∧ 4 = 2 * j) ↔ ∃ k : ℤ, 2 ^ 2 + 4 ^ 2 = 8 * k) := h 2 4
  have h_left : ∃ i j : ℤ, 2 = 2 * i ∧ 4 = 2 * j := by
    refine' ⟨1, 2, _, _⟩
    · norm_num
    · norm_num
  have h_right : ∃ k : ℤ, 2 ^ 2 + 4 ^ 2 = 8 * k := h2.mp h_left
  rcases h_right with ⟨k, hk⟩
  norm_num at hk
  omega
