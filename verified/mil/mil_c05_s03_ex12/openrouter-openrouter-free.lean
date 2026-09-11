import Mathlib

open BigOperators
open Finset

/-- Mathematics in Lean, Chapter 5 §3 (Infinitely Many Primes), exercise 12. Avigad & Massot, Apache-2.0, commit dd6d752. -/
theorem mil_c05_s03_ex12 (Q : ℕ → Prop) [DecidablePred Q] :
    (∃ n, ∀ k, Q k → k ≤ n) → ∃ s : Finset ℕ, ∀ k, Q k ↔ k ∈ s := by
  intro h
  have h_main : ∃ (s : Finset ℕ), ∀ (k : ℕ), Q k ↔ k ∈ s := by
    obtain ⟨n, hn⟩ := h
    let s := Finset.filter (fun k => Q k) (Finset.Iic n)
    refine' ⟨s, _⟩
    intro k
    constructor
    · -- Prove the forward direction: if Q k, then k ∈ s
      intro hq
      have h₁ : k ≤ n := hn k hq
      have h₂ : k ∈ Finset.Iic n := Finset.mem_Iic.mpr h₁
      have h₃ : k ∈ Finset.filter (fun k => Q k) (Finset.Iic n) := by
        apply Finset.mem_filter.mpr
        exact ⟨h₂, hq⟩
      exact h₃
    · -- Prove the reverse direction: if k ∈ s, then Q k
      intro hk
      have h₁ : k ∈ Finset.filter (fun k => Q k) (Finset.Iic n) := hk
      have h₂ : k ∈ Finset.Iic n ∧ Q k := Finset.mem_filter.mp h₁
      exact h₂.2
  exact h_main
