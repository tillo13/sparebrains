import Mathlib

/-- A true statement with a hole instead of a proof. Lean compiles it, but the axiom audit
shows `sorryAx`, so the judge refuses it. This is what every target looks like before a
model has proved it. -/
theorem two_plus_two_sorry : 2 + 2 = 4 := by sorry
