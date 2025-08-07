import Mathlib.Tactic

/-
OKTV 2015/2016, II. kategória, II. forduló, 4. feladat:

Határozzuk meg azokat a pozitív p prímszámokat, amelyekre az alábbi tört értéke
négyzetszám: (2^(p-1))/p
----
bizonyítsuk, hogy a lehetséges megoldások halmaza p={3,7}
-/
lemma exists_sq_factors_if_coprime {x y : ℕ} (h : IsSquare (x*y)) (hc : Nat.Coprime x y) : IsSquare x ∧ IsSquare y := by
  cases x.eq_zero_or_pos <;> cases y.eq_zero_or_pos
  all_goals try simp_all

  have (n : ℕ) : IsSquare n ↔ ∀ p ∈ n.primeFactors, 2 ∣ Nat.factorization n p := by
    constructor
    · intro h p hp
      rw [isSquare_iff_exists_sq n] at h
      obtain ⟨r, hn⟩ := h

      rw [hn, Nat.factorization_pow]
      exact Dvd.intro (r.factorization p) rfl
    · intro h
      refine (isSquare_iff_exists_sq n).mpr ?_

      by_cases h': n = 0
      · use 0
        exact h'
      · let m := ∏ p ∈ n.primeFactors, p ^ (n.factorization p / 2)
        use m

        have : n = m^2 := by
          simp [m]
          rw [← Finset.prod_pow]
          ring_nf

          have h_div_mul : ∀ p ∈ n.primeFactors, p^(n.factorization p / 2 * 2) = p^(n.factorization p) := by
            intro p hp
            have h_div : 2 ∣ n.factorization p := h p hp
            congr
            exact Nat.div_mul_cancel h_div

          have h_n_factor : n = ∏ p ∈ n.primeFactors, p ^ n.factorization p := by
            rw [← Nat.factorization_prod_pow_eq_self h']
            congr
            exact Eq.symm (Nat.factorization_prod_pow_eq_self h')

          rw [h_n_factor]
          apply Finset.prod_congr
          congr
          rw [← h_n_factor]
          exact fun x a ↦ Eq.symm (Mathlib.Tactic.Ring.pow_congr rfl rfl (h_div_mul x a))

        exact this

  apply And.intro
  · rw [this] at h ⊢
    intro p hp
    rw [hc.primeFactors_mul] at h
    specialize h p <| Finset.mem_union_left y.primeFactors hp
    haveI : Fact p.Prime := fact_iff.mpr <| Nat.prime_of_mem_primeFactors hp
    rw [Nat.factorization_mul_apply_of_coprime] at h

    have : y.factorization p = 0 := by
      refine Nat.factorization_eq_zero_of_not_dvd ?_
      refine (Nat.Prime.coprime_iff_not_dvd ?_).mp ?_
      exact Nat.prime_of_mem_primeFactors hp
      refine (Nat.disjoint_primeFactors ?_ ?_).mp ?_
      exact Ne.symm (NeZero.ne' p)
      linarith

      have : p.primeFactors = {p} := by exact Nat.Prime.primeFactors (Nat.prime_of_mem_primeFactors hp)
      rw [this]

      refine Finset.disjoint_singleton_left.mpr ?_
      exact Disjoint.not_mem_of_mem_left_finset (Nat.Coprime.disjoint_primeFactors hc) hp

    rwa [this, add_zero] at h
    exact hc
  · rw [this] at h ⊢
    intro p hp
    rw [hc.primeFactors_mul] at h
    specialize h p <| Finset.mem_union_right x.primeFactors hp
    haveI : Fact p.Prime := fact_iff.mpr <| Nat.prime_of_mem_primeFactors hp
    rw [Nat.factorization_mul_apply_of_coprime] at h

    have : x.factorization p = 0 := by
      refine Nat.factorization_eq_zero_of_not_dvd ?_
      refine (Nat.Prime.coprime_iff_not_dvd ?_).mp ?_
      exact Nat.prime_of_mem_primeFactors hp
      refine (Nat.disjoint_primeFactors ?_ ?_).mp ?_
      exact Ne.symm (NeZero.ne' p)
      linarith

      have : p.primeFactors = {p} := by exact Nat.Prime.primeFactors (Nat.prime_of_mem_primeFactors hp)
      rw [this]

      refine Finset.disjoint_singleton_left.mpr ?_
      exact Disjoint.not_mem_of_mem_right_finset (Nat.Coprime.disjoint_primeFactors hc) hp

    rwa [this, zero_add] at h
    exact hc

lemma square_mod4_neq_3 (a : ℕ) (ha: IsSquare a) : a % 4 ≠ 3 := by
  by_contra! h
  unfold IsSquare at ha
  obtain ⟨r, hr⟩ := ha

  mod_cases h': r%4
  all_goals
    rw [hr] at h
    rw [Nat.mul_mod] at h
    rw [h'] at h
    contradiction

lemma square_mod3_neq_2 (a : ℕ) (ha : IsSquare a) : a % 3 ≠ 2 := by
  by_contra! h
  unfold IsSquare at ha
  obtain ⟨r, hr⟩ := ha

  mod_cases h': r%3
  all_goals
    rw [hr] at h
    rw [Nat.mul_mod] at h
    rw [h'] at h
    contradiction

lemma consec_even_prod_eq_two_pow {a n m: ℕ} (a_geq_1 : a ≥ 1) (h1: 2^n = a+1) (h2: 2^m = a-1) : n=2 ∧ m=1 := by
  have two_pow_diff_eq_2 : 2^n - 2^m = 2 := by omega
  have n_geq_m : 2^n ≥ 2^m := by omega
  have : 2^n ≥ 2^m ↔ n ≥ m := by
    refine Nat.pow_le_pow_iff_right ?_
    norm_num

  rw [this] at n_geq_m

  by_cases h: m > 1
  · have n_gt_1 : n > 1 := by exact Nat.lt_of_lt_of_le h n_geq_m

    have : ∃x, n=x+2 := by exact Nat.exists_eq_add_of_le' n_gt_1
    obtain ⟨x, hx⟩ := this

    have : ∃y, m=y+2 := by exact Nat.exists_eq_add_of_le' h
    obtain ⟨y, hy⟩ := this

    rw [hx, hy] at two_pow_diff_eq_2

    have : 2^(x + 2) - 2^(y + 2) = 4*(2^x - 2^y) := by
      calc
        _ = 4*2^x - 4*2^y := by repeat rw [Nat.pow_succ]; ring_nf
        _ = 4*(2^x - 2^y) := by rw [Nat.mul_sub_left_distrib]

    omega
  · interval_cases m
    · have : a=2 := by omega
      rw [this] at h1

      have h : ∃x, 2^x=3 := by exact ⟨n, h1⟩
      have h_contra : ¬∃x, 2^x=3 := by
        intro ⟨n, hn⟩
        have h1 : 2^1 < 2^n := by rw [hn]; norm_num
        have h2 : 2^n < 2^2 := by rw [hn]; norm_num

        have h3 : 1 < n := Nat.pow_lt_pow_iff_right (by norm_num) |>.mp h1
        have h4 : n < 2 := Nat.pow_lt_pow_iff_right (by norm_num) |>.mp h2

        linarith

      contradiction
    · have two_pow_eq_4: 2^n=2^2 := by omega
      have : 2^n=2^2 ↔ n=2 := by
        refine Nat.pow_right_inj ?_
        norm_num

      rw [this] at two_pow_eq_4
      norm_num
      exact two_pow_eq_4

lemma pow_2_iff_prime_factor_is_2 {a : ℕ} (even_a : Even a) (h : Nat.primeFactors a = {2}) : ∃ x, x>0 ∧ a=2^x := by
  have a_neq_0 : a ≠ 0 := by
    by_contra!
    rw [this] at h
    rw [Nat.primeFactors_zero] at h
    contradiction

  have a_div_2 : 2 ∣ a := by exact even_iff_two_dvd.mp even_a

  use Nat.factorization a 2

  refine And.symm ⟨?_, ?_⟩
  · apply Nat.eq_pow_of_factorization_eq_single a_neq_0 ?_
    apply Finsupp.support_subset_singleton.mp ?_
    exact Finset.subset_of_eq h
  · apply Nat.Prime.factorization_pos_of_dvd ?_ ?_ a_div_2
    exact Nat.prime_two
    exact a_neq_0

theorem oktv2015_ii_ii_iv (p : ℕ) (hp : Nat.Prime p) (hpdiv : p ∣ 2^(p-1) - 1) : p=3 ∨ p=7 ↔ IsSquare ((2^(p-1)-1)/p) := by
  constructor
  · intro h
    simp at h

    rcases h with h | h
    · rw [h]
      norm_num
    · rw [h]
      norm_num

      refine (isSquare_iff_exists_sq 9).mpr ?_
      use 3
      norm_num
  · intro h
    by_cases h': p > 3
    · unfold IsSquare at h
      obtain ⟨r, hr⟩ := h

      have hr : 2 ^ (p - 1) - 1 = r*r*p := by exact Nat.eq_mul_of_div_eq_left hpdiv hr
      have h : 2 ^ (p - 1) - 1 = r*r*p := hr

      have p_odd : Odd p := by
        refine Nat.Prime.odd_of_ne_two hp ?_
        linarith

      obtain ⟨q, hq⟩ := p_odd
      rw [hq] at hr
      norm_num at hr

      rw [pow_mul] at hr
      rw [pow_right_comm] at hr

      have : 1 = 1^2 := by rfl
      rw [this] at hr
      rw [Nat.sq_sub_sq (2 ^ q) 1] at hr

      have : 2 ^ (p - 1) - 1 = (2 ^ q + 1) * (2 ^ q - 1) := by nlinarith

      have p_div_lhs : p ∣ (2 ^ q + 1) ∨ p ∣ (2^q - 1) := by
        refine (Nat.Prime.dvd_mul hp).mp ?_
        rw [← this]
        exact hpdiv

      norm_num at hr
      rw [← hq] at hr

      have q_neq_zero : q ≠ 0 := by
        by_contra!
        rw [this] at hq
        rw [hq] at hp
        norm_num at hp

      have : 2^q ≥ 1 := by exact Nat.one_le_two_pow

      have left_odd : Odd (2 ^ q + 1) := by
        refine Even.add_one ?_
        refine (Nat.even_pow' q_neq_zero).mpr ?_
        exact Nat.even_iff.mpr rfl

      have right_odd : Odd (2 ^ q - 1) := by
        refine Nat.Even.sub_odd ?_ ?_ ?_
        exact Nat.one_le_two_pow
        refine Even.pow_of_ne_zero ?_ q_neq_zero
        repeat norm_num

      have facts_coprime : Nat.Coprime (2 ^ q - 1) (2 ^ q + 1) := by
        have : 2 ^ q + 1 = 2 ^ q - 1 + 2 := by omega
        rw [this]

        refine (Nat.coprime_add_iff_right ?_).mpr ?_
        exact Nat.dvd_refl (2 ^ q - 1)
        exact Nat.coprime_two_right.mpr right_odd

      rcases p_div_lhs with h1 | h1
      · obtain ⟨n, hn⟩ := h1
        have pn_m_2_eq: 2^q - 1 = p*n-2 := by omega
        have p_neq_0 : 0 < p := by exact Nat.zero_lt_of_lt h'

        rw [hn, pn_m_2_eq] at hr
        rw [hn, pn_m_2_eq, Nat.coprime_comm] at facts_coprime

        have factors_coprime : Nat.Coprime n (p*n-2) := by exact Nat.Coprime.coprime_mul_left facts_coprime
        have prod_sq : IsSquare (n*(p*n-2)) := by
          ring_nf at hr
          rw [Nat.mul_assoc] at hr
          rw [Nat.mul_left_cancel_iff p_neq_0] at hr
          rw [hr]

          exact IsSquare.sq r

        have : IsSquare n ∧ IsSquare (p*n-2) := by exact exists_sq_factors_if_coprime prod_sq factors_coprime
        obtain ⟨n_sq, pn_m_2_sq⟩ := this

        have right_fact_mod_4: (p*n - 2) % 4 = 3 := by
          rw [← pn_m_2_eq]

          have : (2 ^ q - 1) % 4 = 3 ↔ (2 ^ q + 3) % 4 = 3 := by omega
          rw [this, Nat.add_mod]

          have : 2 ^ q % 4 = 0 := by
            have : ∃x, q = x+2 := by exact Nat.exists_eq_add_of_le' (by linarith)
            obtain ⟨x, hx⟩ := this
            rw [hx, Nat.pow_succ, Nat.pow_succ]
            ring_nf
            exact Nat.mul_mod_left (2 ^ x) 4
          rw [this]

        have : ¬ IsSquare (p * n - 2) := by
          by_contra!
          have : (p * n - 2) % 4 ≠ 3 := by exact square_mod4_neq_3 (p * n - 2) pn_m_2_sq
          contradiction

        contradiction
      · obtain ⟨n, hn⟩ := h1
        have q_neq_zero : q ≠ 0 := by
          by_contra!
          rw [this] at hq
          rw [hq] at hp
          norm_num at hp

        have p_neq_0 : 0 < p := by exact Nat.zero_lt_of_lt h'

        have h2qp1_eq : 2^q + 1 = p*n+2 := by
          refine Nat.eq_add_of_sub_eq ?_ hn
          refine Nat.le_add_right_of_le ?_
          exact Nat.le_self_pow q_neq_zero 2

        rw [hn, h2qp1_eq] at hr
        rw [hn, h2qp1_eq] at facts_coprime

        have : (p * n + 2) * (p * n) = (n*(p*n+2))*p := by ring

        have factors_coprime : Nat.Coprime n (p*n+2) := by exact Nat.Coprime.coprime_mul_left facts_coprime
        have prod_sq : IsSquare (n*(p*n+2)) := by
          rw [this] at hr
          rw [Nat.mul_right_cancel_iff p_neq_0] at hr
          rw [hr]

          exact IsSquare.mul_self r

        have : IsSquare n ∧ IsSquare (p*n+2) := by exact exists_sq_factors_if_coprime prod_sq factors_coprime
        obtain ⟨n_sq, pn_m_2_sq⟩ := this

        have p_mod_4_eq_3 : p % 4 = 3 := by
          mod_cases h'': p % 4
          · rw [Nat.ModEq] at h''
            have : 4 ∣ p := by exact Nat.dvd_of_mod_eq_zero h''

            omega
          · rw [Nat.ModEq] at h''
            have : 4 ∣ p-1 := by exact (Nat.modEq_iff_dvd' p_neq_0).mp (id (Eq.symm h''))
            have : ∃k, p=4*k+1 := by
              use (p-1)/4
              omega

            obtain ⟨k, hk⟩ := this
            have hkq : q = 2*k := by linarith

            have pnp2_mod_3 : (p * n + 2) % 3 = 2 := by
              rw [← h2qp1_eq, hkq, Nat.pow_mul, Nat.add_mod, Nat.pow_mod]
              norm_num

            have : ¬ IsSquare (p * n + 2) := by
              by_contra!
              have : (p * n + 2) % 3 ≠ 2 := by exact square_mod3_neq_2 (p * n + 2) pn_m_2_sq
              contradiction

            contradiction
          · rw [Nat.ModEq] at h''
            have hp_geq_2 : 2≤p := by exact Nat.Prime.two_le hp
            have : 4 ∣ p-2 := by exact (Nat.modEq_iff_dvd' hp_geq_2).mp (id (Eq.symm h''))

            omega
          · exact h''

        have : p ≥ 3 := by exact Nat.le_of_succ_le h'
        have : 4 ∣ p-3 := by exact (Nat.modEq_iff_dvd' this).mp (id (Eq.symm p_mod_4_eq_3))

        have : ∃k, p=4*k+3 := by
            use (p-3)/4
            omega

        obtain ⟨k, hk⟩ := this
        have : q = 2*k+1 := by linarith

        rw [← h2qp1_eq] at pn_m_2_sq
        rw [this] at pn_m_2_sq
        rw [isSquare_iff_exists_sq (2 ^ (2 * k + 1) + 1)] at pn_m_2_sq

        obtain ⟨a, ha⟩ := pn_m_2_sq

        have : 2 ^ (2 * k + 1) = a^2 - 1^2 := by exact Eq.symm (Nat.sub_eq_of_eq_add (id (Eq.symm ha)))
        rw [Nat.sq_sub_sq] at this

        have h_fact_eq : Nat.primeFactors ((a + 1) * (a - 1)) = Nat.primeFactors (2 ^ (2 * k + 1)) := by
          exact congrArg Nat.primeFactors (id (Eq.symm this))

        have lhs_fact : Nat.primeFactors (2 ^ (2 * k + 1)) = {2} := by
          refine Nat.primeFactors_prime_pow ?_ ?_
          linarith
          exact Nat.prime_two

        have rhs_div_2 : Even ((a+1)*(a-1)) := by
          rw [← this]
          rw [Nat.pow_succ]
          norm_num

        have a_neq_0 : a ≠ 0 := by
          by_contra!
          rw [this] at ha
          contradiction

        have a_geq_1 : a ≥ 1 := by exact Nat.one_le_iff_ne_zero.mpr a_neq_0

        have ap1_div_2 : Even (a+1) := by
          by_contra! h
          rw [Nat.not_even_iff_odd] at h

          have : Odd (a+1-2) := by
            refine Nat.Odd.sub_even ?_ h ?_
            omega
            exact Nat.even_iff.mpr rfl

          have : Odd (a-1) := by exact this
          have : Odd ((a+1) * (a-1)) := by exact Odd.mul h this
          have : ¬ Even ((a+1)*(a-1)) := by exact Nat.not_even_iff_odd.mpr this

          contradiction

        have am1_div_2 : Even (a-1) := by
          by_contra! h
          rw [Nat.not_even_iff_odd] at h

          have : Odd (a-1+2) := by
            rw [Nat.odd_add]
            refine Iff.symm (iff_of_true ?_ h)
            exact Nat.even_iff.mpr rfl

          have : Odd (a+1) := by
            have aa : a-1+2 = a+1 := by omega
            rw [aa] at this
            exact this

          have : Odd ((a+1) * (a-1)) := by exact Odd.mul this h
          have : ¬ Even ((a+1)*(a-1)) := by exact Nat.not_even_iff_odd.mpr this

          contradiction

        have : Nat.primeFactors ((a + 1) * (a - 1)) = {2} ↔ Nat.primeFactors (a+1) = {2} ∧ Nat.primeFactors (a-1) = {2} := by
          have a_neq_1 : 1 < a := by
            by_contra!
            interval_cases a
            all_goals
              have : 2 ^ (2 * k + 1) > 0 := by exact Nat.two_pow_pos (2 * k + 1)
              omega

          rw [Nat.primeFactors_mul]
          constructor
          · intro h
            have : 2 ∣ (a-1) := by exact even_iff_two_dvd.mp am1_div_2
            have two_in_am1_facs: 2 ∈ (a-1).primeFactors := by
              apply (Nat.mem_primeFactors_of_ne_zero ?_).mpr ?_
              · refine Nat.sub_ne_zero_of_lt ?_
                exact a_neq_1
              · exact ite_else_self.mp this

            constructor
            · apply Finset.eq_of_subset_of_card_le
              · rw [← h]
                exact Finset.subset_union_left
              · have : ({2} : Finset ℕ).card = 1 := by norm_num
                rw [this]
                refine Finset.one_le_card.mpr ?_
                refine Nat.nonempty_primeFactors.mpr ?_
                omega
            · apply Finset.eq_of_subset_of_card_le
              · rw [← h]
                exact Finset.subset_union_right
              · have : ({2} : Finset ℕ).card = 1 := by norm_num
                rw [this]
                refine Finset.one_le_card.mpr ?_
                refine Nat.nonempty_primeFactors.mpr ?_
                have : 1 < a - 1 := by
                  by_contra!
                  have : a ≤ 2 := by exact Nat.le_succ_of_pred_le this
                  interval_cases a
                  all_goals norm_num at two_in_am1_facs
                exact this
          · intro h
            obtain ⟨ap1, am1⟩ := h

            rw [ap1, am1]
            rfl

          exact Ne.symm (Nat.zero_ne_add_one a)
          refine Nat.sub_ne_zero_iff_lt.mpr ?_
          exact a_neq_1

        rw [lhs_fact] at h_fact_eq
        rw [this] at h_fact_eq

        obtain ⟨ap1_primes, am1_primes⟩ := h_fact_eq

        have : ∃x, x>0 ∧ a+1 = 2^x := by exact pow_2_iff_prime_factor_is_2 ap1_div_2 ap1_primes
        obtain ⟨x, ⟨hxpos, hx⟩⟩ := this

        have : ∃y, y>0 ∧ a-1 = 2^y := by exact pow_2_iff_prime_factor_is_2 am1_div_2 am1_primes
        obtain ⟨y, ⟨hypos, hy⟩⟩ := this

        have : x=2 ∧ y=1 := by exact consec_even_prod_eq_two_pow a_geq_1 hx.symm hy.symm
        obtain ⟨x_val, y_val⟩ := this

        rw [x_val] at hx

        have : a = 3 := by exact Nat.succ_inj'.mp hx
        rw [this] at ha

        have exp : 2 ^ (2 * k + 1) = 2^3 := by linarith
        have : 2 ^ (2 * k + 1) = 2^3 ↔ 2 * k + 1 = 3 := by
          refine Nat.pow_right_inj ?_
          norm_num
        rw [this] at exp

        have : k = 1 := by linarith
        rw [this] at hk
        norm_num at hk

        exact Or.inr hk
    · interval_cases p
      repeat contradiction
      norm_num
