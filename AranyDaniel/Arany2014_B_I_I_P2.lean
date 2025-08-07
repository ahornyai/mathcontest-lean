import Mathlib.Tactic

/-
Arany Dániel 2014/2015 Kezdők I. kategória I. forduló II. feladat

Melyek azok a p, q pozitív prímszámok, melyekre p^2 - 1 osztható q-val, és q^2 - 1 osztható
p-vel?
----------------------
Bizonyítsuk, hogy a megoldáshalmaz : ⟨p, q⟩ ∈ {(2,3), (3,2)}
-/
lemma prime_diff_eq_1 {p q : ℕ} (hp : Nat.Prime p) (hq : Nat.Prime q) (h : p=q+1) : p=3 ∧ q=2 := by
  have : q = p-1 := by exact Nat.eq_sub_of_add_eq (id (Eq.symm h))

  by_cases h1: Odd q
  · have hp_neq_2 : p ≠ 2 := by
      intro hp_eq
      rw [hp_eq] at this
      norm_num at this
      rw [this] at hq

      exact Nat.prime_one_false hq

    have : ¬ Odd q := by
      refine Nat.not_odd_iff_even.mpr ?_
      rw [this]
      exact Nat.Prime.even_sub_one hp hp_neq_2

    contradiction
  · have : Even q := by exact Nat.not_odd_iff_even.mp h1
    have hq_eq : q=2 := by exact (Nat.Prime.even_iff hq).mp this

    omega

theorem arany2014_beginner_i_i_ii (p q : ℤ) (hppos : p > 0) (hqpos : q > 0) (hp : Prime p) (hq : Prime q)
  : (q ∣ p^2 - 1 ∧ p ∣ q^2 - 1) ↔ ⟨p, q⟩ ∈ ({(2,3), (3,2)} : Set (ℤ × ℤ)) := by
  simp

  constructor
  · intro h
    obtain ⟨h1, h2⟩ := h

    have : (1 : ℤ) = 1^2 := by exact rfl

    rw [this, sq_sub_sq] at h1 h2

    have hnprime1 : ¬ Prime 1 := by exact not_prime_one

    have hq_neq_1 : q ≠ 1 := by
      intro h
      rw [h] at hq
      refine Nat.prime_one_false ?_
      exact Nat.prime_iff_prime_int.mpr hq

    have hp_neq_1 : p ≠ 1 := by
      intro h
      rw [h] at hp
      refine Nat.prime_one_false ?_
      exact Nat.prime_iff_prime_int.mpr hp

    have hqdiv : q ∣ (p+1) ∨ q ∣ (p-1) := by exact (Prime.dvd_mul hq).mp h1
    have hpdiv : p ∣ (q+1) ∨ p ∣ (q-1) := by exact (Prime.dvd_mul hp).mp h2

    have hq_le_p1 : q ≤ p+1 := by
      rcases hqdiv with h3 | h3
      · apply Int.le_of_dvd (by linarith) h3
      · have : q ≤ p-1 := by
          apply Int.le_of_dvd
          have : 1 < p := by
            by_contra!
            interval_cases p
            (expose_names; exact hp_neq_1 this_1)

          omega
          exact h3

        omega

    have hp_le_q1 : p ≤ q+1 := by
      rcases hpdiv with h3 | h3
      · apply Int.le_of_dvd (by linarith) h3
      · have : p ≤ q-1 := by
          apply Int.le_of_dvd
          have : 1 < q := by
            by_contra!
            interval_cases q
            (expose_names; exact hq_neq_1 this_1)

          omega
          exact h3

        omega

    have : p=q ∨ p+1 = q ∨ q+1 = p := by omega

    have hp_nat : ∃n : ℕ, p=n := by refine Int.eq_ofNat_of_zero_le (by exact Int.le_of_lt hppos)
    have hq_nat : ∃n : ℕ, q=n := by refine Int.eq_ofNat_of_zero_le (by exact Int.le_of_lt hqpos)

    obtain ⟨pn, hpn⟩ := hp_nat
    obtain ⟨qn, hqn⟩ := hq_nat

    have hqnp : Nat.Prime qn := by
      refine Nat.prime_iff_prime_int.mpr ?_
      rw [← hqn]
      exact hq

    have hpnp : Nat.Prime pn := by
      refine Nat.prime_iff_prime_int.mpr ?_
      rw [← hpn]
      exact hp

    rcases this with h3 | h3 | h3
    · rw [h3] at h1
      rw [← sq_sub_sq] at h1

      have : q ∣ q^2 := by exact Dvd.intro_left (q.pow 1) rfl
      have : q ∣ 1 := by exact (Int.dvd_iff_dvd_of_dvd_sub h1).mp this
      obtain ⟨k, hk⟩ := this

      have : q=1 ∨ q=-1 := by exact Int.eq_one_or_neg_one_of_mul_eq_one (id (Eq.symm hk))

      rcases this with h4 | h4
      · exact False.elim (hq_neq_1 h4)
      · linarith
    · rw [hpn, hqn] at h3
      rw [hpn, hqn]
      norm_cast at *

      symm at h3
      left
      symm

      apply prime_diff_eq_1 hqnp hpnp h3
    · rw [hpn, hqn] at h3
      rw [hpn, hqn]
      norm_cast at *

      symm at h3
      right

      apply prime_diff_eq_1 hpnp hqnp h3
  · intro h
    rcases h with h | h
    all_goals
      obtain ⟨rfl, rfl⟩ := h
      norm_num
