import Mathlib

open scoped Nat
open scoped Real

/-- How many integers between 15 and 85 are divisible by 20? -/
theorem mathd_numbertheory_12 :
    Finset.card (Finset.filter (fun x => 20 ∣ x) (Finset.Icc 15 85)) = 4 := by
  have : (Finset.filter (fun x => 20 ∣ x) (Finset.Icc 15 85)) = ({20, 40, 60, 80} : Finset ℕ) := by
    ext n
    simp [Finset.mem_filter, Finset.mem_Icc, Finset.mem_insert, Finset.mem_singleton]
    omega
  rw [this]
  rfl
