import Mathlib

open scoped Nat
open scoped Real

/--
We write $\lfloor X \rfloor$ to mean the greatest integer less than or equal to $X$; for example $\lfloor 3\frac{1}{2} \rfloor = 3$. If $N = \frac{1}{3}$, what is the value of $\lfloor 10N \rfloor + \lfloor 100N \rfloor + \lfloor 1000N \rfloor + \lfloor 10,000N \rfloor$? -/
theorem mathd_algebra_153 (n : ℝ) (h₀ : n = 1 / 3) :
    Int.floor (10 * n) + Int.floor (100 * n) + Int.floor (1000 * n) + Int.floor (10000 * n) =
      3702 := by
  have h1 : Int.floor (10 * n) = 3 := by
    simpa [h₀] using (by norm_num : Int.floor (10 * (1 / 3 : ℝ)) = 3)
  have h2 : Int.floor (100 * n) = 33 := by
    simpa [h₀] using (by norm_num : Int.floor (100 * (1 / 3 : ℝ)) = 33)
  have h3 : Int.floor (1000 * n) = 333 := by
    simpa [h₀] using (by norm_num : Int.floor (1000 * (1 / 3 : ℝ)) = 333)
  have h4 : Int.floor (10000 * n) = 3333 := by
    simpa [h₀] using (by norm_num : Int.floor (10000 * (1 / 3 : ℝ)) = 3333)
  calc
    Int.floor (10 * n) + Int.floor (100 * n) + Int.floor (1000 * n) + Int.floor (10000 * n)
        = 3 + 33 + 333 + 3333 := by
          simp [h1, h2, h3, h4]
    _ = 3702 := by norm_num
