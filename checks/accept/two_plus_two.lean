import Mathlib

/-- The smallest possible example of what the judge accepts: a true statement with a
complete proof. `norm_num` evaluates both sides; the kernel checks the result. -/
theorem two_plus_two : 2 + 2 = 4 := by norm_num
