import Mathlib.Tactic
import Mathlib.Algebra.Group.Even

/-
OKTV 2018/2019, III. kategória, I. forduló, 2. feladat:

Keressük meg az összes nemnegatív egész számokból álló k, l, m szám-
hármast, amelyre 13^k + 43^l = 2018^m
-/
theorem oktv_2018_iii_2 (k l m : ℕ) : m = 1 ∧ l = 2 ∧ k = 2 ↔ 13^k + 43^l = 2018^m := by
  constructor
  · intro h
    obtain ⟨rfl, rfl, rfl⟩ := h
    norm_num
  · intro h
    have m_odd : m % 2 = 1 := by
      by_contra!

      have : m%2=0 := by exact Nat.mod_two_ne_one.mp this
      have : 2∣m := by exact Nat.dvd_of_mod_eq_zero this

      obtain ⟨x, hx⟩ := this

      rw [hx] at h
      rw [Nat.pow_mul] at h

      have lhs_mod_3_two : (13 ^ k + 43 ^ l) % 3 = 2 := by
        rw [Nat.add_mod]
        rw [Nat.pow_mod]
        norm_num

        rw [Nat.add_mod]
        rw [Nat.pow_mod]
        norm_num

      have rhs_mod_3_one : (2018 ^ 2) ^ x % 3 = 1 := by
        rw [Nat.pow_mod]
        norm_num

      omega

    have k_even : k%2=0 := by
      by_contra!
      have : k%2=1 := by exact Nat.mod_two_ne_zero.mp this

      have : ∃x : ℕ, k = 2 * x + 1 := by
        use (k-1)/2
        omega

      obtain ⟨x, hx⟩ := this

      rw [hx, Nat.pow_succ] at h

      have lhs_mod_7 : (13 ^ (2 * x) * 13 + 43 ^ l) % 7 = 0 := by
        have : 43^l %7 = 1 := by rw[Nat.pow_mod]; norm_num

        rw [Nat.add_mod]
        rw [Nat.mul_mod]
        rw [Nat.pow_mul]
        rw [Nat.pow_mod]
        rw [this]
        norm_num

      have rhs_mod_7 : 2018^m % 7 ≠ 0 := by
        by_contra!
        rw [Nat.pow_mod] at this
        norm_num at this

        have : 7 ∣ 2^m := by exact Nat.dvd_of_mod_eq_zero this
        have no_div : ¬ 7 ∣ 2^m := by
          refine (Nat.Prime.coprime_iff_not_dvd ?_).mp ?_
          norm_num
          exact Nat.Coprime.pow_right m rfl

        contradiction

      omega

    have : 2 ∣ k := by exact Nat.dvd_of_mod_eq_zero k_even
    obtain ⟨x, hx⟩ := this

    have lhs_mod_8 : (13 ^ k + 43 ^ l) % 8 = 2 ∨ (13 ^ k + 43 ^ l) % 8 = 4 := by
      mod_cases l%2
      · refine Or.inl ?_
        have : 2 ∣ l := by exact Nat.dvd_of_mod_eq_zero H
        obtain ⟨y, hy⟩ := this

        rw [hy, hx]
        rw [Nat.pow_mul, Nat.pow_mul, Nat.add_mod, Nat.pow_mod]
        norm_num

        rw [Nat.add_mod, Nat.pow_mod]
        norm_num
      · refine Or.inr ?_
        rw [Nat.ModEq] at H
        norm_num at H

        have : l ≠ 0 := by
          by_contra!
          rw [this] at H
          contradiction

        have : 2 ∣ l-1 := by
          refine (Nat.modEq_iff_dvd' ?_).mp (id (Eq.symm H))
          exact Nat.one_le_iff_ne_zero.mpr this

        have : ∃y : ℕ, l = 2 * y + 1 := by
          use (l-1)/2
          omega

        obtain ⟨y, hy⟩ := this

        rw [hx, hy, Nat.pow_succ, Nat.pow_mul]
        rw [Nat.add_mod, Nat.pow_mod]
        norm_num

        rw [Nat.pow_mul, Nat.add_mod, Nat.mul_mod, Nat.pow_mod]
        norm_num

    have m_le_3 : m < 3 := by
      by_contra!
      obtain ⟨y,hy⟩ := by exact Nat.exists_eq_add_of_le' this

      have : 2018^m%8 = 0 := by
        rw [hy]
        repeat rw [Nat.pow_succ]
        omega

      omega

    have m_eq_1 : m = 1 := by omega
    rw [m_eq_1] at h

    have h13k_gt_0 : 13^k > 0 := by exact Nat.pos_of_neZero (13 ^ k)

    have l_leq_2: l ≤ 2 := by
      by_contra!

      have : ∃y, l=y+3 := by exact Nat.exists_eq_add_of_le' this
      obtain ⟨y, hy⟩ := this

      rw [hy] at h
      repeat rw [Nat.pow_succ] at h

      have : 43 ^ y > 0 := by exact Nat.pos_of_neZero (43 ^ y)

      omega

    interval_cases l
    · have h : ∃ n, 13 ^ n = 2017 := ⟨k, by linarith⟩
      have h_contra: ¬ ∃ n, 13 ^ n = 2017 := by
        intro ⟨n, hn⟩
        have h1 : 13^2 < 13^n := by rw [hn]; norm_num
        have h2 : 13^n < 13^3 := by rw [hn]; norm_num

        have h3 : 2 < n := Nat.pow_lt_pow_iff_right (by norm_num) |>.mp h1
        have h4 : n < 3 := Nat.pow_lt_pow_iff_right (by norm_num) |>.mp h2

        linarith

      contradiction
    · have h : ∃ n, 13 ^ n = 1975 := ⟨k, by linarith⟩
      have h_contra: ¬ ∃ n, 13 ^ n = 1975 := by
        intro ⟨n, hn⟩
        have h1 : 13^2 < 13^n := by rw [hn]; norm_num
        have h2 : 13^n < 13^3 := by rw [hn]; norm_num

        have h3 : 2 < n := Nat.pow_lt_pow_iff_right (by norm_num) |>.mp h1
        have h4 : n < 3 := Nat.pow_lt_pow_iff_right (by norm_num) |>.mp h2

        linarith

      contradiction
    · have k_eq_2: 13^k = 13^2 ↔ k=2 := by
        refine Nat.pow_right_inj ?_
        norm_num
      have : 13^k = 13^2 := by linarith
      rw [k_eq_2] at this

      omega
