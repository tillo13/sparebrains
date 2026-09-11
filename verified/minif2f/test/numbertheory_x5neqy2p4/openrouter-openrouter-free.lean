import Mathlib

open scoped Nat
open scoped Real

theorem numbertheory_x5neqy2p4 (x y : ℤ) : x ^ 5 ≠ y ^ 2 + 4 := by
  intro h
  have hmod : (x : ZMod 11)^5 = (y : ZMod 11)^2 + 4 := by
    simpa using congrArg (fun z : ℤ => (z : ZMod 11)) h
  -- Or more directly: 
  -- have hmod : (x : ZMod 11)^5 = (y : ZMod 11)^2 + 4 := by
  --   simpa using congr (mod 11) h? 
  -- Actually, we can use `Int.modEq`? 
  -- Let's use `map_eq`:
  -- `Int.cast_pow` etc.
  -- We can use `norm_num`? 
  -- Simpler: 
  -- have hmod := congr (fun z : ℤ => (z : ZMod 11)) h
  -- simpa using hmod
  -- But we need to know that casting distributes over powers and addition.
  -- In Mathlib, `Int.cast_pow` etc. exist.
  -- So:
  have hmod : (x : ZMod 11)^5 = (y : ZMod 11)^2 + 4 := by
    simpa using congrArg (fun z : ℤ => (z : ZMod 11)) h
  -- Then we have a contradiction because we can prove:
  have contra : ∀ x y : ZMod 11, x^5 ≠ y^2 + 4 := by
    decide
  exact contra _ _ hmod
