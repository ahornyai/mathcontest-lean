import Mathlib.Tactic

/-
OKTV 2023/2024, I. kategória, II. forduló, 3. feladat:

Határozza meg azokat a p és q pozitív prímszámokat, amelyekre
log₂(q-1) + log₄(q+1) = 1 + 3*log₈(p)
----------------------------------------
Bizonyítsuk, hogy az egyedüli a megoldás a p=2, q=3.
-/
theorem eq_of_mul_eq_sixteen {x y : ℕ} (h : x * y = 16) :
    x = 1 ∧ y = 16 ∨ x = 2 ∧ y = 8 ∨ x = 4 ∧ y = 4 ∨ x = 8 ∧ y = 2 ∨ x = 16 ∧ y = 1 := by
  have h₁ : (x, y) ∈ Nat.divisorsAntidiagonal 16 := by simpa using h
  have h₂ : Nat.divisorsAntidiagonal 16 = {(1, 16), (2, 8), (4, 4), (8, 2), (16, 1)} := by rfl
  simpa [h₂] using h₁

theorem oktv2023_i_ii_iii {p q : ℕ} (hp : Nat.Prime p) (hq : Nat.Prime q) :
  Real.logb 2 (q-1) + Real.logb 4 (q+1) = 1 + 3 * Real.logb 8 (p) ↔ (p=2 ∧ q=3) := by
  constructor
  · intro h

    have hq_geq_1 : q ≥ 1 := by exact Nat.Prime.one_le hq
    have hp_sq_real_pos : (p : ℝ)^2 > 0 := by
      norm_cast
      refine Nat.pow_pos ?_
      exact Nat.Prime.pos hp
    have hqm1_sq_pos : (q - 1) ^ 2 > 0 := by
      refine Nat.pow_pos ?_
      exact Nat.zero_lt_sub_of_lt (by exact Nat.Prime.one_lt hq)

    have h₁ : Real.logb 4 (q+1) = (Real.logb 2 (q+1))/2 := by
      simp [Real.logb]
      field_simp
      left
      rw [mul_comm, ← Real.log_rpow]
      all_goals norm_num

    have h₂ : 3 * Real.logb 8 (p) = Real.logb 2 (p) := by
      simp [Real.logb]
      field_simp

      rw [show 3 * Real.log p * Real.log 2 = Real.log p * (3 * Real.log 2) by ring]

      have : 3 * Real.log 2 = Real.log 8 := by
        rw [← Real.log_rpow]
        all_goals norm_num
      rw [this]

    have h₃ : Real.logb 2 ((q-1)^2) + Real.logb 2 (q+1) = Real.logb 2 4 + Real.logb 2 (p^2) := by
      rw [h₁, h₂] at h
      field_simp at h

      have : (1 + Real.logb 2 p) * 2 = 2 + (2 : ℕ) * Real.logb 2 p := by ring
      rw [this, ← Real.logb_pow] at h

      have : Real.logb 2 4 = 2 := by
        rw [show (4 : ℝ)=2^2 by norm_num]
        rw [Real.logb_pow]
        simp
      rw [this]

      have : Real.logb 2 (q - 1) * 2 = (2 : ℕ) * Real.logb 2 (q - 1) := by ring
      rw [this, ← Real.logb_pow] at h

      exact h

    have h₄ : (q-1)^2 * (q+1) = 4*p^2 := by
      repeat rw [← Real.logb_mul] at h₃
      apply Real.logb_injOn_pos at h₃

      norm_cast at h₃
      norm_num
      norm_num
      norm_cast
      refine Nat.mul_pos ?_ ?_
      exact hqm1_sq_pos
      exact Nat.add_pos_left hq_geq_1 1
      norm_num
      exact hp_sq_real_pos
      norm_num
      exact Ne.symm (ne_of_lt hp_sq_real_pos)
      norm_cast
      exact Nat.ne_zero_of_lt hqm1_sq_pos
      exact Nat.cast_add_one_ne_zero q

    have h₅ : Odd q := by
      by_contra!
      have hq_even : Even q := by exact Nat.not_odd_iff_even.mp this
      have hq_eq_2 : q = 2 := by exact (Nat.Prime.even_iff hq).mp hq_even
      rw [hq_eq_2] at h₄
      omega

    have hp_eq : p = 2 := by
      obtain ⟨k, hk⟩ := h₅
      rw [hk] at h₄

      have h_div_8 : 8 ∣ 4*p^2 := by
        rw [← h₄]
        rw [show 2 * k + 1 - 1 = 2*k by rfl]
        rw [show (2 * k) ^ 2 * (2 * k + 1 + 1) = 8*(k^2*(k+1)) by ring]

        exact Nat.dvd_mul_right 8 (k ^ 2 * (k + 1))
      obtain ⟨l, hl⟩ := h_div_8

      have : p^2 = l + l := by omega
      have : Even (p^2) := by
        refine (even_iff_exists_add_self (p ^ 2)).mpr ?_
        use l

      rw [Nat.even_pow] at this
      have hp_even : Even p := this.left
      exact (Nat.Prime.even_iff hp).mp hp_even

    have hq_eq : q = 3 := by
      rw [hp_eq] at h₄
      norm_num at h₄

      apply eq_of_mul_eq_sixteen at h₄
      rcases h₄ with h₄ | h₄ | h₄ | h₄ | h₄
      · have : q = 15 := by linarith
        rw [this] at hq
        contradiction
      · have : q = 7 := by linarith
        rw [this] at h₄
        contradiction
      · omega
      · have : q = 1 := by linarith
        rw [this] at hq
        contradiction
      · omega

    exact ⟨hp_eq, hq_eq⟩
  · intro h
    obtain ⟨rfl, rfl⟩ := h
    norm_num

    have : (3 : ℕ) * Real.logb 8 2 = 1 := by
      rw [← Real.logb_pow]
      norm_num

    norm_cast at this
    rw [this]
    norm_num
