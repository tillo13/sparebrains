import Mathlib

/-- The smallest possible example of what the judge refuses: a false statement. No tactic
can prove it, so Lean stops with an error and the file never reaches the axiom audit. -/
theorem two_plus_two_is_five : 2 + 2 = 5 := by norm_num
