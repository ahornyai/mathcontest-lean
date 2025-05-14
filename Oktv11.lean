import Mathlib.Tactic
import Mathlib.Algebra.Group.Even

/-
OKTV 2010/2011, I. kategória, I. forduló, 4. feladat:

Mely pozitív p prímszámokra teljesül, hogy 360 osztója a p^4 - 5*p^2 + 4 kifejezésnek?
--
bizonyítsuk be, hogy minden prímszám megoldás, kivéve a 3 és az 5
-/
lemma div_8_consec_even {a : ℕ} (H: Even a ∧ Even (a+2)) : 8 ∣ a*(a+2) := by
  mod_cases h': a%4
  · unfold Nat.ModEq at h'
    have ha_div_4 : 4 ∣ a := by exact Nat.dvd_of_mod_eq_zero h'

    obtain ⟨m, hm⟩ := ha_div_4
    have : 4 * m * (4 * m + 2) = 8*(2*m^2 + m) := by ring

    rw [hm]
    rw [this]

    exact Nat.dvd_mul_right 8 (2 * m ^ 2 + m)
  · unfold Nat.ModEq at h'
    obtain ⟨k, Hk⟩ := H.left

    rw [Hk] at h'

    have : (k + k) % 4 ≠ 1 := by omega

    exfalso
    contradiction
  · unfold Nat.ModEq at h'
    have (ha : a%4 = 2) : 4∣(a+2) := by omega
    have ha_plus_2_div_4 : 4 ∣ (a+2) := by exact this h'

    obtain ⟨m, hm⟩ := ha_plus_2_div_4
    obtain ⟨k, hk⟩ := H.left

    have : (k + k) * (4 * m) = 8*(k*m) := by ring

    rw [hm]
    rw [hk]
    rw [this]

    exact Nat.dvd_mul_right 8 (k * m)
  · unfold Nat.ModEq at h'
    obtain ⟨k, Hk⟩ := H.left

    rw [Hk] at h'

    have : (k + k) % 4 ≠ 3 := by omega

    exfalso
    contradiction

theorem oktv_2014_i_3 (p : ℕ) (hp : Nat.Prime p) (hp_neq_3_and_5 : p≠3 ∧ p≠5) : 360 ∣ (p^4 - 5*p^2 + 4 : ℤ) := by
  ---have : (p^4 - 5*p^2 + 4 : ℤ) = (p^2 - 1)*(p^2 - 4) := by ring
  have : (p^4 - 5*p^2 + 4 : ℤ) = (p - 1)*(p + 1)*(p - 2)*(p+2) := by ring

  rw [this]

  obtain ⟨hp_neq_3, hp_neq_5⟩ := hp_neq_3_and_5

  by_cases h: p > 5
  · have p_odd : Odd p := by
      refine Nat.Prime.odd_of_ne_two ?_ ?_
      exact hp
      linarith

    have p_plus_1_even : Even (p+1) := by exact Odd.add_one p_odd
    have p_minus_1_even : Even (p-1) := by
      refine Nat.Prime.even_sub_one hp ?_
      linarith
    have p_minus_1_plus_2_even : Even (p-1+2) := by
      refine Nat.even_add.mpr ?_
      constructor
      · intro h
        exact Nat.even_iff.mpr rfl
      · intro h
        exact p_minus_1_even

    have p_both_even : Even (p-1) ∧ Even (p-1+2) := ⟨p_minus_1_even, p_minus_1_plus_2_even⟩
    have p_minus_1_plus_2_eq : p-1+2 = p+1 := by omega

    have : 8 ∣ (p-1)*(p-1+2) := by exact div_8_consec_even p_both_even
    have : 8 ∣ (p-1)*(p+1) := by rw [p_minus_1_plus_2_eq] at this; exact this
    have h_div_8 : 8 ∣ (p - 1) * (p + 1) * (p - 2) * (p + 2) := by
      obtain ⟨k,hk⟩ := this
      rw [hk]
      ring_nf
      omega

    have h_div_9: 9 ∣ (p - 1) * (p + 1) * (p - 2) * (p + 2) := by
      mod_cases h': p % 3
      · unfold Nat.ModEq at h'
        have hp_div_3 : 3 ∣ p := by exact Nat.dvd_of_mod_eq_zero h'

        obtain ⟨k,hk⟩ := hp_div_3
        rw [hk] at hp

        have : ¬Nat.Prime (3 * k) := by
          refine Nat.not_prime_mul ?_ ?_
          norm_num
          omega

        contradiction
      · unfold Nat.ModEq at h'
        have p_minus_1_div_3 : 3 ∣ (p-1) := by
          refine (Nat.modEq_iff_dvd' ?_).mp (id (Eq.symm h'))
          exact Nat.one_le_of_lt h

        obtain ⟨k,hk⟩ := p_minus_1_div_3

        have : p+2 = p - 1 + 3 := by linarith
        rw [this]
        rw [hk]

        have : 3 * k * (p + 1) * (p - 2) * (3 * k + 3) = 9*(k * (p + 1) * (p - 2) * (k + 1)) := by ring
        rw [this]

        exact Nat.dvd_mul_right 9 (k * (p + 1) * (p - 2) * (k + 1))
      · unfold Nat.ModEq at h'
        have p_minus_2_div_3 : 3 ∣ (p-2) := by
          refine (Nat.modEq_iff_dvd' ?_).mp (id (Eq.symm h'))
          exact Nat.Prime.two_le hp

        obtain ⟨k,hk⟩ := p_minus_2_div_3

        have : p+1 = p-2+3 := by omega
        rw [this]
        rw [hk]

        have : (p - 1) * (3 * k + 3) * (3 * k) * (p + 2) = 9*((p - 1) * (k + 1) * k * (p + 2)) := by ring
        rw [this]

        exact Nat.dvd_mul_right 9 ((p - 1) * (k + 1) * k * (p + 2))

    have h_div_5 : 5 ∣ (p - 1) * (p + 1) * (p - 2) * (p + 2) := by
      mod_cases h': p%5
      · unfold Nat.ModEq at h'
        have hp_div_5 : 5 ∣ p := by exact Nat.dvd_of_mod_eq_zero h'

        obtain ⟨k,hk⟩ := hp_div_5
        rw [hk] at hp

        have : ¬Nat.Prime (5 * k) := by
          refine Nat.not_prime_mul ?_ ?_
          norm_num
          omega

        contradiction
      · unfold Nat.ModEq at h'
        have p_minus_1_div_5 : 5 ∣ (p-1) := by
          refine (Nat.modEq_iff_dvd' ?_).mp (id (Eq.symm h'))
          exact Nat.one_le_of_lt h

        obtain ⟨k,hk⟩ := p_minus_1_div_5

        rw [hk]
        ring_nf
        omega
      · unfold Nat.ModEq at h'
        have p_minus_2_div_5 : 5 ∣ (p-2) := by
          refine (Nat.modEq_iff_dvd' ?_).mp (id (Eq.symm h'))
          exact Nat.Prime.two_le hp

        obtain ⟨k,hk⟩ := p_minus_2_div_5

        rw [hk]
        ring_nf
        omega
      · unfold Nat.ModEq at h'
        have (hp: p%5 = 3) : 5∣(p+2) := by omega
        have : 5∣(p+2) := by exact this h'

        obtain ⟨k,hk⟩ := this

        rw [hk]
        ring_nf
        omega
      · unfold Nat.ModEq at h'
        have (hp: p%5 = 4) : 5∣(p+1) := by omega
        have : 5∣(p+1) := by exact this h'

        obtain ⟨k,hk⟩ := this

        rw [hk]
        ring_nf
        omega

    have h_div_40 : 40 ∣ (p - 1) * (p + 1) * (p - 2) * (p + 2) := by
      exact Nat.Coprime.mul_dvd_of_dvd_of_dvd rfl h_div_5 h_div_8

    have h_nat_div_360 : 360 ∣ (p - 1) * (p + 1) * (p - 2) * (p + 2) := by
      exact Nat.Coprime.mul_dvd_of_dvd_of_dvd rfl h_div_40 h_div_9

    have (ha : 360 ∣ ((p - 1) * (p + 1) * (p - 2) * (p + 2) : ℕ)) : 360 ∣ ((p - 1) * (p + 1) * (p - 2) * (p + 2) : ℤ) := by
      have h_coe : ((p - 1 : ℤ) * (p + 1 : ℤ)* (p - 2 : ℤ)*(p+2 : ℤ)) = ↑((p - 1)*(p+1)*(p - 2)*(p+2)) := by
        rw [Int.ofNat_mul]
        rw [Int.ofNat_mul]
        rw [Int.ofNat_sub (by linarith)]
        rw [Int.ofNat_mul]
        rw [Int.ofNat_sub (by linarith)]
        norm_cast

      rw [h_coe]
      exact Int.ofNat_dvd_right.mpr h_nat_div_360

    exact this h_nat_div_360
  · norm_num at h
    match p with
    | 0 =>
      exfalso
      have : ¬Prime 0 := by exact not_prime_zero
      contradiction
    | 2 => norm_num
    | 4 =>
      exfalso
      have : ¬Prime 4 := by
        refine IsSquare.not_prime ?_
        refine (isSquare_iff_exists_sq 4).mpr ?_
        use 2
        norm_num

      contradiction
    | p+6 => contradiction
