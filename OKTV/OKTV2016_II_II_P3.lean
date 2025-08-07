import Mathlib.Tactic
import Mathlib.Algebra.Group.Even
import Mathlib.Tactic.LinearCombination

/-
OKTV 2016/2017, II. kategória, II. forduló, 3. feladat:

Határozzuk meg, mely a, b, c nemnegatív egész számok esetén teljesül:
3^a + 17 * 4^b = c^2
---
bizonyítsuk be, hogy az egyetlen megoldás: a = 0, b = 3, c = 33
-/

/- these two from: https://github.com/dwrensha/compfiles/blob/78fc982dd2bb9d4bde3ea85588835d16319f246a/Compfiles/Poland2016S1P8.lean#L72 -/
lemma even_of_add { a b : ℕ } (ha : Even a) (hb : Even (a + b)) : Even b := by
  rw [show b = a + b - a by omega]
  exact Even.tsub hb ha

lemma div_4_mul_of_both_even {a b : ℕ } (H : Even a ∧ Even b) : 4 ∣ a * b := by
  obtain ⟨k, Hk⟩ := H.left
  obtain ⟨l, Hl⟩ := H.right
  use k * l
  rw[Hk]
  rw[Hl]
  ring

/- my own lemmas -/
lemma square_mod3_neq_2 (a : ℕ) : a^2 % 3 ≠ 2 := by
  by_contra! h
  mod_cases h': a%3
  all_goals
    rw [Nat.pow_mod a] at h
    rw [h'] at h
    contradiction

lemma two_pow_mul_odd (x y : ℕ) (h₁ : Even x) (h₂ : Odd y)
  : ∀ b, 2^b = x * y → y = 1 := by
  intro b
  rintro heq
  by_contra! hy

  obtain ⟨a, ha⟩ := h₁

  have ha : x = 2 * a := by omega

  have a_neq_zero : a ≠ 0 := by
    by_contra!
    rw [this] at ha
    rw [ha] at heq
    norm_num at heq

  have y_neq_zero : y ≠ 0 := by
    by_contra!
    rw [this] at heq
    norm_num at heq

  have b_neq_zero : b ≠ 0 := by
    by_contra! hb

    rw [hb] at heq
    norm_num at heq
    rw [ha] at heq

    have : y * (2 * a) > 1 := by
      refine Right.one_lt_mul_of_le_of_lt ?_ ?_
      repeat omega

    linarith

  have b_pos : b ≥ 1 := by omega

  have h_div_y : y ∣ 2^b := by exact Dvd.intro_left x (id (Eq.symm heq))

  obtain ⟨k, hk⟩ := h₂

  have coprime : Nat.Coprime (2 * k + 1) (2^b) := by
      apply Nat.Coprime.symm
      refine Nat.Coprime.pow_left b ?_
      exact (Nat.coprime_mul_left_add_right 2 1 k).mpr rfl

  rw [← hk, Nat.coprime_iff_gcd_eq_one] at coprime

  have y_dvd_one : y ∣ 1 := by
    refine Nat.dvd_one.mpr ?_
    exact Nat.Coprime.eq_one_of_dvd coprime h_div_y

  have y_eq_one : y = 1 := by exact Nat.eq_one_of_dvd_one y_dvd_one

  omega

lemma not_pow_two_18 : ¬ ∃ n, 2 ^ n = 18 := by
  intro ⟨n, hn⟩
  have h1 : 2^4 < 2^n := by
    rw [hn]
    norm_num -- Shows 16 < 18
  have h2 : 2^n < 2^5 := by
    rw [hn]
    norm_num -- Shows 18 < 32
  -- Now convert the power inequalities to exponent inequalities
  have h3 : 4 < n := Nat.pow_lt_pow_iff_right (by norm_num) |>.mp h1
  have h4 : n < 5 := Nat.pow_lt_pow_iff_right (by norm_num) |>.mp h2
  -- But there's no integer between 4 and 5
  omega

theorem oktv2016_ii_ii_iii : ∀ (a b c : ℕ), 3^a + 17 * 4^b = c^2 → (a, b, c) = (0, 3, 33) := by
  intro a b c
  rintro heq

  have c_neq_zero: c ≠ 0 := by
    by_contra! h
    rw [h] at heq
    simp at heq

  have a_eq_zero : a = 0 := by
    by_contra! h
    have a_pos : a > 0 := by omega
    have mod3_3a : 3^a % 3 = 0 := by
      have : 3 ∣ 3^a := by
        exists 3^(a-1)
        rw [← pow_succ', Nat.sub_add_cancel]
        exact a_pos
      exact Nat.dvd_iff_mod_eq_zero.mp this

    have mod3_4b : 4^b % 3 = 1 := by
      rw [Nat.pow_mod 4 b 3]
      norm_num

    have : (c^2) % 3 = 2 := by omega
    apply square_mod3_neq_2 at this

    contradiction

  rw [a_eq_zero] at heq
  norm_num at heq

  have sq_diff : 17 * 4 ^ b = c ^ 2 - 1 := by omega
  have sq_diff_fac : 17 * 4 ^ b = (c+1) * (c-1) := by
    rw [sq_diff]
    apply Nat.sq_sub_sq c 1

  have b_neq_zero : b ≠ 0 := by
    by_contra! h

    rw [h] at heq
    norm_num at heq

    have : ¬ ∃ a, 18 = a^2 := by {
      intro h
      obtain ⟨a, ha⟩ := h

      have gt_4_sq : 4^2 < a^2 := by omega
      have lt_5_sq : a^2 < 5^2 := by omega

      apply Nat.not_exists_sq' gt_4_sq lt_5_sq
      exact exists_apply_eq_apply (fun a ↦ a ^ 2) a
    }

    exact this ⟨c, heq⟩

  have b_pos : b > 0 := by omega

  have left_rw_pow_2 : 17 * 4^b = 17 * 2^(2*b) := by
    norm_num
    exact Eq.symm (Mathlib.Tactic.Ring.pow_nat rfl rfl rfl)

  have left_even : (17 * 4^b) % 2 = 0 := by
    refine Nat.even_iff.mp ?_
    refine Nat.even_mul.mpr ?_
    refine Or.inr ?_
    refine Even.pow_of_ne_zero ?_ ?_

    exact Nat.even_iff.mpr rfl
    omega

  have right_even : (c+1) * (c-1) % 2 = 0 := by
    rw [← sq_diff_fac]
    exact left_even

  have right_even_def : Even ((c+1) * (c-1)) := by exact Nat.even_iff.mpr right_even

  -- possible factorizations, since 17 is prime:
  -- 17 * 2 = c + 1 and 2^(2*b) = c - 1
  -- 17 * 2 = c - 1 and 2^(2*b) = c + 1
  have h₁ :  17 * 2 ^ (2*b) = (c + 1) * (c - 1) := by
    rw [← left_rw_pow_2]
    exact sq_diff_fac

  have : 2 ^ (2*b - 1 + 1) = 2 ^ (2*b) := by
    norm_num
    omega

  have h₂ : 17 * 2 * 2 ^ (2*b - 1) = (c + 1) * (c - 1) := by
    rw [← h₁]
    calc
      _ = 17 * 2 ^ (2*b - 1 + 1) := by omega
      _ = 17 * 2 ^ (2*b) := by rw [this]

  have both_factors_even_c_1 : Even (c + 1) ∧ Even (c - 1) := by
    have either_even : (Even (c + 1) ∨ Even (c - 1)) :=
      Nat.even_mul.mp right_even_def
    obtain c_plus_1_even | c_minus_1_even := either_even
    · have : Even ((c + 1) + (c - 1)) := by
        use c
        rw [show (c + 1) + (c - 1) = 2 * c by omega]
        ring
      have m_minus_k_even : Even (c - 1) := even_of_add c_plus_1_even this
      constructor
      · exact c_plus_1_even
      · exact m_minus_k_even

    · have : Even ((c - 1) + (c + 1)) := by
        use c
        omega
      have c_plus_1_even : Even (c + 1) := even_of_add c_minus_1_even this
      constructor
      · exact c_plus_1_even
      · exact c_minus_1_even

  have div_2_cp1 : 2 ∣ (c+1) := by
    refine Even.two_dvd ?_
    exact both_factors_even_c_1.left

  have div_2_cm1 : 2 ∣ (c-1) := by
    refine Even.two_dvd ?_
    exact both_factors_even_c_1.right

  have div_17_cp1_or_cm1 : 17 ∣ (c+1) ∨ 17 ∣ (c-1) := by
    refine (Nat.Prime.dvd_mul ?_).mp ?_
    exact Nat.properDivisors_eq_singleton_one_iff_prime.mp rfl
    omega

  have div_17_2_cp1_or_cm1 : 17 * 2 ∣ (c+1) ∨ 17 * 2 ∣ (c-1) := by omega

  have h_34_nonzero : 0 < 17 * 2 := by norm_num

  cases' div_17_2_cp1_or_cm1 with div_cp1 div_cm1
  -- I. case: 17 * 2 ∣ (c + 1)
  · rcases div_cp1 with ⟨k, hk⟩
    rw [hk] at h₂

    have h_simpl : 2^(2*b - 1) = k * (c - 1) := by
      rw [← Nat.mul_left_cancel_iff h_34_nonzero]
      linarith

    have k_dist : k * (c - 1) = k * (c+1) - 2*k := by
      calc
        _ = k * (c - 1) := by omega
        _ = k * c - k := by exact Nat.mul_sub_one k c
        _ = k * c + k - 2*k := by omega
        _ = k * (c + 1) - 2*k := by exact rfl

    rw [k_dist] at h_simpl
    rw [hk] at h_simpl

    have two_exp : 2 ^ (2 * b - 1) = k * (17 * k - 1) * 2 := by
      rw [h_simpl]
      simp [Nat.mul_sub_left_distrib, Nat.mul_sub_right_distrib, ← mul_assoc]
      rw [show 34 = 2 * 17 by rfl]
      ring_nf

    have b_geq_two : 2 * b ≥ 2 := by omega
    have : 2 * b - 1 = (2*b - 2) + 1 := by omega

    have main_eq : 2 ^ (2 * b - 2) = k * (17 * k - 1) := by
      rw [this, pow_succ] at two_exp
      omega

    have main_eq_comm : 2 ^ (2 * b - 2) = (17 * k - 1) * k := by linarith

    have k_neq_zero : k ≠ 0 := by omega

    -- Now we consider two cases, I.: k is even, II.: k is odd
    cases' Nat.even_or_odd k with k_even k_odd
    · have h_17k_even : Even (17 * k) := by exact Even.mul_left k_even 17
      have h_odd : Odd (17 * k - 1) := by
        refine Nat.Even.sub_odd ?_ h_17k_even ?_
        omega
        exact Nat.odd_iff.mpr rfl

      have : 17 * k - 1 = 1 := by
        apply two_pow_mul_odd k (17*k - 1)
        · exact k_even
        · exact h_odd
        · exact main_eq

      omega
    · have h_17k_odd : Odd (17 * k) := by
        refine Odd.mul ?_ k_odd
        exact Nat.odd_iff.mpr rfl

      have h_even : Even (17 * k - 1) := by
        refine Nat.Odd.sub_odd h_17k_odd ?_
        exact Nat.odd_iff.mpr rfl

      have : k = 1 := by
        apply two_pow_mul_odd (17*k - 1) k
        · exact h_even
        · exact k_odd
        · exact main_eq_comm

      rw [this] at hk
      norm_num at hk

      rw [this] at main_eq
      norm_num at main_eq

      rw [show 16 = 2^4 by norm_num] at main_eq

      have : 2 * b - 2 = 4 := by apply Nat.pow_right_injective (by decide) main_eq

      have b_val : b = 3 := by omega
      have c_val : c = 33 := by omega

      refine Prod.mk.inj_iff.mpr ?_
      constructor
      · exact a_eq_zero
      · exact Prod.ext b_val c_val
  -- II. case: 17 * 2 ∣ (c - 1)
  · rcases div_cm1 with ⟨k, hk⟩
    rw [hk] at h₂

    have h_simpl : 2^(2*b - 1) = k * (c + 1) := by
      rw [← Nat.mul_left_cancel_iff h_34_nonzero]
      linarith

    have c_neq_zero : c ≠ 0 := by
      by_contra!
      rw [this] at heq
      norm_num at heq

    have k_dist : k * (c + 1) = k * (c-1) + 2*k := by
      calc
        _ = k * (c + 1) := by omega
        _ = k * c + k := by exact Nat.mul_add_one k c
        _ = k * c + 2 * k - k := by omega
        _ = k * c - k + 2 * k := by
          refine Nat.sub_add_comm ?_;
          refine le_mul_of_le_of_one_le ?_ ?_
          omega
          omega
        _ = k * (c - 1) + 2*k := by
          refine Nat.add_right_cancel_iff.mpr ?_
          exact Eq.symm (Nat.mul_sub_one k c)


    rw [k_dist] at h_simpl
    rw [hk] at h_simpl

    have two_exp : 2 ^ (2 * b - 1) = k * (17 * k + 1) * 2 := by
      rw [h_simpl]
      simp [Nat.mul_sub_left_distrib, Nat.mul_sub_right_distrib, ← mul_assoc]
      rw [show 34 = 2 * 17 by rfl]
      ring_nf

    have b_geq_two : 2 * b ≥ 2 := by omega
    have : 2 * b - 1 = (2*b - 2) + 1 := by omega

    have main_eq : 2 ^ (2 * b - 2) = k * (17 * k + 1) := by
      rw [this, pow_succ] at two_exp
      omega

    have main_eq_comm : 2 ^ (2 * b - 2) = (17 * k + 1) * k := by linarith

    have k_neq_zero : k ≠ 0 := by
      by_contra!
      rw [this] at main_eq
      norm_num at main_eq

    -- Now we consider two cases, I.: k is even, II.: k is odd
    cases' Nat.even_or_odd k with k_even k_odd
    · have h_17k_even : Even (17 * k) := by exact Even.mul_left k_even 17
      have h_odd : Odd (17 * k + 1) := by exact Even.add_one h_17k_even

      have : 17 * k + 1 = 1 := by
        apply two_pow_mul_odd k (17*k + 1)
        · exact k_even
        · exact h_odd
        · exact main_eq

      omega
    · have h_17k_odd : Odd (17 * k) := by
        refine Odd.mul ?_ k_odd
        exact Nat.odd_iff.mpr rfl

      have h_even : Even (17 * k + 1) := by exact Odd.add_one h_17k_odd

      have : k = 1 := by
        apply two_pow_mul_odd (17*k + 1) k
        · exact h_even
        · exact k_odd
        · exact main_eq_comm

      rw [this] at hk
      norm_num at hk

      rw [this] at main_eq
      norm_num at main_eq

      have h_contra : ∃ n, 2 ^ n = 18 := ⟨2 * b - 2, main_eq⟩
      have h_contra' : ¬ ∃ n, 2 ^ n = 18 := by apply not_pow_two_18

      contradiction
