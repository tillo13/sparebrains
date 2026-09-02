import Mathlib

open scoped Nat
open scoped Real

/--
Find the value of $a_2 + a_4 + a_6 + \dots + a_{98}$ if $a_1$, $a_2$, $a_3$, $\dots$ is an arithmetic progression with common difference 1, and $a_1 + a_2 + a_3 + \dots + a_{98} = 137$. -/
theorem aime_1984_p1 (u : ℕ → ℚ) (h₀ : ∀ n, u (n + 1) = u n + 1)
    (h₁ : ∑ k ∈ Finset.range 98, u k.succ = 137) : ∑ k ∈ Finset.range 49, u (2 * k.succ) = 93 := by
  have h_u_formula : ∀ n : ℕ, u n = u 0 + n := by
    intro n
    have h₂ : ∀ n : ℕ, u n = u 0 + n := by
      intro n
      induction n with
      | zero => simp
      | succ n ih =>
        have h₃ := h₀ n
        simp [ih, Nat.cast_add, Nat.cast_one] at h₃ ⊢
        <;> ring_nf at h₃ ⊢ <;> linarith
    exact h₂ n
  
  have h_sum_98 : 98 * u 0 + 4851 = 137 := by
    have h₂ : ∑ k ∈ Finset.range 98, u k.succ = 137 := h₁
    have h₃ : ∑ k ∈ Finset.range 98, u k.succ = ∑ k ∈ Finset.range 98, (u 0 + (k + 1 : ℚ)) := by
      apply Finset.sum_congr rfl
      intro k hk
      have h₄ : u k.succ = u 0 + (k + 1 : ℚ) := by
        have h₅ : u k.succ = u (k + 1) := by simp [Nat.succ_eq_add_one]
        rw [h₅]
        have h₆ : u (k + 1) = u 0 + (k + 1 : ℚ) := by
          have h₇ : u (k + 1) = u 0 + (k + 1 : ℕ) := by
            have h₈ := h_u_formula (k + 1)
            norm_cast at h₈ ⊢
            <;> simp_all [add_assoc]
            <;> ring_nf at *
            <;> linarith
          norm_cast at h₇ ⊢
          <;> simp_all [add_assoc]
          <;> ring_nf at *
          <;> linarith
        rw [h₆]
        <;> norm_cast
        <;> simp_all [add_assoc]
        <;> ring_nf at *
        <;> linarith
      rw [h₄]
      <;> simp_all [add_assoc]
      <;> ring_nf at *
      <;> linarith
    rw [h₃] at h₂
    have h₄ : ∑ k ∈ Finset.range 98, (u 0 + (k + 1 : ℚ)) = 98 * u 0 + ∑ k ∈ Finset.range 98, (k + 1 : ℚ) := by
      calc
        ∑ k ∈ Finset.range 98, (u 0 + (k + 1 : ℚ)) = ∑ k ∈ Finset.range 98, (u 0 + (k + 1 : ℚ)) := rfl
        _ = ∑ k ∈ Finset.range 98, (u 0 : ℚ) + ∑ k ∈ Finset.range 98, (k + 1 : ℚ) := by
          rw [Finset.sum_add_distrib]
        _ = 98 * u 0 + ∑ k ∈ Finset.range 98, (k + 1 : ℚ) := by
          simp [Finset.sum_const, Finset.card_range]
          <;> ring_nf
          <;> field_simp
          <;> ring_nf
    rw [h₄] at h₂
    have h₅ : ∑ k ∈ Finset.range 98, (k + 1 : ℚ) = 4851 := by
      norm_num [Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_succ]
      <;> rfl
    rw [h₅] at h₂
    linarith
  
  have h_u0 : u 0 = -2357 / 49 := by
    have h₂ : 98 * u 0 + 4851 = 137 := h_sum_98
    have h₃ : 98 * u 0 = -4714 := by linarith
    have h₄ : u 0 = -2357 / 49 := by
      norm_num at h₃ ⊢
      <;> ring_nf at h₃ ⊢ <;> norm_num at h₃ ⊢ <;>
      (try norm_num) <;>
      (try linarith) <;>
      (try field_simp at h₃ ⊢ <;> ring_nf at h₃ ⊢ <;> norm_num at h₃ ⊢ <;> linarith)
      <;>
      (try
        {
          norm_num at h₃ ⊢
          <;>
          (try linarith)
          <;>
          (try ring_nf at h₃ ⊢ <;> norm_num at h₃ ⊢ <;> linarith)
        })
    exact h₄
  
  have h_sum_49 : ∑ k ∈ Finset.range 49, u (2 * k.succ) = 49 * u 0 + 2450 := by
    have h₂ : ∑ k ∈ Finset.range 49, u (2 * k.succ) = ∑ k ∈ Finset.range 49, (u 0 + (2 * (k + 1 : ℚ))) := by
      apply Finset.sum_congr rfl
      intro k hk
      have h₃ : u (2 * k.succ) = u 0 + (2 * (k + 1 : ℚ)) := by
        have h₄ : u (2 * k.succ) = u (2 * (k + 1)) := by
          simp [Nat.succ_eq_add_one, mul_add, add_mul, mul_one, mul_assoc]
          <;> ring_nf at *
          <;> norm_num at *
          <;> linarith
        rw [h₄]
        have h₅ : u (2 * (k + 1)) = u 0 + (2 * (k + 1 : ℚ)) := by
          have h₆ : u (2 * (k + 1)) = u 0 + (2 * (k + 1 : ℕ)) := by
            have h₇ := h_u_formula (2 * (k + 1))
            norm_cast at h₇ ⊢
            <;> simp_all [add_assoc]
            <;> ring_nf at *
            <;> linarith
          norm_cast at h₆ ⊢
          <;> simp_all [add_assoc]
          <;> ring_nf at *
          <;> linarith
        rw [h₅]
        <;> norm_cast
        <;> simp_all [add_assoc]
        <;> ring_nf at *
        <;> linarith
      rw [h₃]
      <;> simp_all [add_assoc]
      <;> ring_nf at *
      <;> linarith
    rw [h₂]
    have h₃ : ∑ k ∈ Finset.range 49, (u 0 + (2 * (k + 1 : ℚ))) = 49 * u 0 + ∑ k ∈ Finset.range 49, (2 * (k + 1 : ℚ)) := by
      calc
        ∑ k ∈ Finset.range 49, (u 0 + (2 * (k + 1 : ℚ))) = ∑ k ∈ Finset.range 49, (u 0 : ℚ) + ∑ k ∈ Finset.range 49, (2 * (k + 1 : ℚ)) := by
          rw [Finset.sum_add_distrib]
        _ = 49 * u 0 + ∑ k ∈ Finset.range 49, (2 * (k + 1 : ℚ)) := by
          simp [Finset.sum_const, Finset.card_range]
          <;> ring_nf
          <;> field_simp
          <;> ring_nf
    rw [h₃]
    have h₄ : ∑ k ∈ Finset.range 49, (2 * (k + 1 : ℚ)) = 2450 := by
      norm_num [Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_succ]
      <;> rfl
    rw [h₄]
    <;> ring_nf
    <;> norm_num
    <;> linarith
  
  have h_final : ∑ k ∈ Finset.range 49, u (2 * k.succ) = 93 := by
    rw [h_sum_49]
    rw [h_u0]
    <;> norm_num
    <;> linarith
  
  apply h_final
