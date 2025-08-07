import Mathlib.Tactic

/-
Arany Dániel 2015/2016 Kezdők III. kategória, 2. (döntő) forduló 1. feladat

Oldjuk meg a p^α = 2^β + 1 egyenletet, ahol α, β 1-nél nagyobb egész számok, p^α pedig
egy prímhatvány.
----------------------
Bizonyítsuk, hogy az egyetlen lehetséges megoldás a p=3 α=2 β=3 számhármas
-/
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

lemma pow_2_iff_prime_factor_is_2 {a : ℕ} (h : Nat.primeFactors a = {2}) : ∃ x, x>0 ∧ a=2^x := by
  have : 2 ∈ Nat.primeFactors a := by
    rw [h]
    exact Finset.mem_singleton.mpr rfl

  have a_div_2 : 2 ∣ a := by exact Nat.dvd_of_mem_primeFactors this

  have a_neq_0 : a ≠ 0 := by
    by_contra!
    rw [this] at h
    rw [Nat.primeFactors_zero] at h
    contradiction

  use Nat.factorization a 2

  refine And.symm ⟨?_, ?_⟩
  · apply Nat.eq_pow_of_factorization_eq_single a_neq_0 ?_
    apply Finsupp.support_subset_singleton.mp ?_
    exact Finset.subset_of_eq h
  · apply Nat.Prime.factorization_pos_of_dvd ?_ ?_ a_div_2
    exact Nat.prime_two
    exact a_neq_0

theorem arany2015_beginner_iii_ii_i {p a b : ℕ} (hp : Nat.Prime p) (ha : a > 1) (hb : b > 1)
  : p^a = 2^b + 1 ↔ p=3 ∧ a=2 ∧ b=3 := by
  constructor
  · intro h
    have hp_neq_2 : p ≠ 2 := by
      by_contra!
      rw [this] at h

      have hlhs_even : Even (2^a) := by
        refine (Nat.even_pow' ?_).mpr ?_
        exact Nat.ne_zero_of_lt ha
        exact Nat.even_iff.mpr rfl

      have hrhs_odd : ¬ Even (2^b + 1) := by
        refine Nat.not_even_iff_odd.mpr ?_
        refine Even.add_odd ?_ ?_
        refine (Nat.even_pow' ?_).mpr ?_
        exact Nat.ne_zero_of_lt hb
        exact Nat.even_iff.mpr rfl
        exact Nat.odd_iff.mpr rfl

      rw [h] at hlhs_even
      contradiction

    have hp_gt_2 : p > 2 := by
      by_contra!
      interval_cases p
      all_goals contradiction

    by_cases ha_parity : Even a
    · obtain ⟨k, hk⟩ := ha_parity

      have hk : a = k*2 := by omega

      have h1 : (p^k)^2 - 1^2 = 2^b := by
        rw [← Nat.pow_mul, ← hk]
        exact Eq.symm (Nat.eq_sub_of_add_eq (id (Eq.symm h)))
      rw [Nat.sq_sub_sq] at h1

      have h2 : ((p ^ k + 1) * (p ^ k - 1)).primeFactors = {2} := by
        rw [h1]

        refine Nat.primeFactors_prime_pow ?_ ?_
        linarith
        exact Nat.prime_two

      have hpkp1_primes : Nat.primeFactors (p^k+1) = {2} := by
        apply Finset.eq_of_subset_of_card_le
        rw [← h2]

        refine Nat.primeFactors_mono ?_ ?_
        exact Nat.dvd_mul_right (p ^ k + 1) (p ^ k - 1)
        rw [h1]
        exact Ne.symm (NeZero.ne' (2 ^ b))

        have : ({2} : Finset ℕ).card = 1 := by norm_num
        rw [this]
        refine Finset.one_le_card.mpr ?_
        refine Nat.nonempty_primeFactors.mpr ?_

        have : p^k ≠ 0 := by
          by_contra!
          have : p=0 := by exact pow_eq_zero this
          rw [this] at hp
          contradiction

        omega

      have hpkm1_primes : Nat.primeFactors (p^k-1) = {2} := by
        apply Finset.eq_of_subset_of_card_le
        rw [← h2]

        refine Nat.primeFactors_mono ?_ ?_
        exact Nat.dvd_mul_left (p ^ k - 1) (p ^ k + 1)
        rw [h1]
        exact Ne.symm (NeZero.ne' (2 ^ b))

        have : ({2} : Finset ℕ).card = 1 := by norm_num
        rw [this]
        refine Finset.one_le_card.mpr ?_
        refine Nat.nonempty_primeFactors.mpr ?_

        have : p^k > 2 := by
          refine Nat.two_lt_of_ne ?_ ?_ ?_

          by_contra!
          have : p=0 := by exact pow_eq_zero this
          rw [this] at hp
          contradiction

          by_contra!
          rw [pow_eq_one_iff] at this
          rw [this] at hp
          contradiction
          linarith

          by_contra!
          rw [this] at hpkp1_primes
          norm_num at hpkp1_primes

        omega

      /- import lemmas from oktv20 -/
      obtain ⟨x, ⟨hxpos, hx⟩⟩ := pow_2_iff_prime_factor_is_2 hpkp1_primes
      obtain ⟨y, ⟨hypos, hy⟩⟩ := pow_2_iff_prime_factor_is_2 hpkm1_primes

      symm at hx hy

      have : x=2 ∧ y=1 := by
        have : p^k ≥ 1 := by refine Nat.one_le_pow k p (by linarith)
        exact consec_even_prod_eq_two_pow this hx hy
      obtain ⟨rfl, rfl⟩ := this


      have h3 : p^k=3 := by omega

      have hk_eq : k = 1 := by
        by_contra! h4
        have : ¬ Nat.Prime 3 := by
          rw [← h3]
          exact Nat.Prime.not_prime_pow' h4

        contradiction

      have ha_eq : a = 2 := by omega

      have hp_eq : p=3 := by
        rw [hk_eq] at h3
        norm_num at h3
        exact h3

      have hb_eq : b=3 := by
        have : 2^b = 2^3 := by
          rw [hp_eq, ha_eq] at h
          omega
        rw [Nat.pow_right_inj (by decide)] at this

        exact this

      exact ⟨hp_eq, ⟨ha_eq, hb_eq⟩⟩
    · rw [Nat.not_even_iff_odd] at ha_parity
      obtain ⟨k, hk⟩ := ha_parity

      have : ∃ p1 : ℤ, p = p1 := by exact exists_eq'
      obtain ⟨p1, hp1⟩ := this

      have h3 : p1^a - 1 = 2^b := by
        rw [← hp1]
        linarith
      rw [← geom_sum_mul, ← hp1] at h3

      have : p ≥ 1 := by omega
      norm_cast at h3

      have ha_succ : a = (a-1) + 1 := by omega

      have h3_left_odd : Odd (∑ i ∈ Finset.range a, p ^ i) := by
        rw [ha_succ, Finset.sum_range_succ']

        refine Even.add_odd ?_ (by exact Nat.odd_iff.mpr rfl)
        refine Nat.even_iff.mpr ?_

        have : (∑ i ∈ Finset.range (a - 1), p ^ (i + 1) % 2) % 2 = (∑ i ∈ Finset.range (a - 1), 1) % 2 := by
          congr
          refine funext ?_
          intro x

          refine Nat.odd_iff.mp ?_
          refine Odd.pow ?_
          exact Nat.Prime.odd_of_ne_two hp hp_neq_2
        rw [Finset.sum_nat_mod, this]

        have : (∑ i ∈ Finset.range (a - 1), 1) = (a-1) := by
          have : ∀x, (∑ i ∈ Finset.range x, 1) = x := by
            exact fun x => Finset.sum_range_induction (fun k => 1) (fun x => x) rfl (congrFun rfl) x

          specialize this (a-1)
          exact this

        rw [this, hk]

        omega

      have : (∑ i ∈ Finset.range a, p ^ i) = 1 := by
        have : (∑ i ∈ Finset.range a, p ^ i).primeFactors = ∅ := by
          have h2_union : ((∑ x ∈ Finset.range a, p ^ x) * (p - 1)).primeFactors = {2} := by
            rw [h3, Nat.primeFactors_prime_pow]
            omega
            exact Nat.prime_two

          rw [Nat.primeFactors_mul] at h2_union

          have h2_notin_h3_left : 2 ∉ (∑ x ∈ Finset.range a, p ^ x).primeFactors := by
            by_contra!
            have : 2 ∣ (∑ x ∈ Finset.range a, p ^ x) := by exact Nat.dvd_of_mem_primeFactors this
            have : ¬ Odd ((∑ x ∈ Finset.range a, p ^ x)) := by
              refine Nat.not_odd_iff_even.mpr ?_
              exact (even_iff_exists_two_nsmul (∑ x ∈ Finset.range a, p ^ x)).mpr this

            contradiction

          refine Finset.eq_empty_of_forall_notMem ?_
          intro x
          by_contra! h5

          have : x ∈ ({2} : Finset ℕ) := by
              rw [← h2_union]
              exact Finset.mem_union_left (p - 1).primeFactors h5
          have : x=2 := by exact Nat.mem_Ioc_succ.mp this
          rw [this] at h5

          contradiction
          exact Nat.ne_of_odd_add h3_left_odd
          omega

        rw [Nat.primeFactors_eq_empty] at this

        rcases this with h4 | h4
        · rw [h4] at h3_left_odd
          contradiction
        · exact h4

      rw [ha_succ, Finset.sum_range_succ'] at this

      have : ∑ k ∈ Finset.range (a - 1), p ^ (k + 1) > 0 := by
        refine Nat.zero_lt_of_ne_zero ?_
        by_contra! h4
        rw [Finset.sum_eq_zero_iff] at h4

        have : p=0 := by
          specialize h4 0

          have : p^(0+1) = p := by ring
          rw [this] at h4

          have : 0 ∈ Finset.range (a-1) := by
            refine Finset.mem_range.mpr ?_
            linarith

          exact h4 this

        rw [this] at hp
        contradiction

      linarith
  · intro h
    obtain ⟨rfl, rfl, rfl⟩ := h
    norm_num
