import Mathlib

open scoped Nat
open scoped Real

/-- What is the remainder when $2000+2001+2002+2003+2004+2005+2006$ is divided by $7$? -/
theorem mathd_numbertheory_345 : (2000 + 2001 + 2002 + 2003 + 2004 + 2005 + 2006) % 7 = 0 := by
  simp only [add_assoc, add_left_comm, add_right_comm]
  norm_num
