import Mathlib.Tactic

/-
Arany Dániel 2015/2016 Kezdők III. kategória, 2. (döntő) forduló 1. feladat

Oldjuk meg a p^α = 2^β + 1 egyenletet, ahol α, β 1-nél nagyobb egész számok, p^α pedig
egy prímhatvány.
----------------------
Bizonyítsuk, hogy az egyetlen lehetséges megoldás a p=3 α=2 β=3 számhármas
-/

lemma finset_sum_range_one_eq {a : ℕ} : (∑ i ∈ Finset.range a, 1) = a := by
  exact Finset.sum_range_induction (fun k => 1) (fun {a} => a) rfl (congrFun rfl) a

theorem arany2016_beginner_iii_ii_i {p a b : ℕ} (hp : Nat.Prime p) (ha : a > 1) (hb : b > 1)
  : p^a = 2^b + 1 ↔ p=3 ∧ a=2 ∧ b=3 := by
  constructor
  · intro h
    /-
    have : IsPrimePow (2^b + 1) := by
      rw [← h]

      refine (isPrimePow_pow_iff ?_).mpr ?_
      linarith
      exact Nat.Prime.isPrimePow hp
    -/

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
          have : p = 2 := by
            have hk_neq_0 : k ≠ 0 := by linarith
            rw [← Nat.pow_left_inj hk_neq_0]
            rw [this]
            
            sorry
          
          contradiction
      
        omega
      
      /- import lemmas from oktv20 -/
      sorry
    · rw [Nat.not_even_iff_odd] at ha_parity
      obtain ⟨k, hk⟩ := ha_parity

      have : ∃ p1 : ℤ, p = p1 := by exact exists_eq'
      obtain ⟨p1, hp1⟩ := this

      have h3 : p1^a - 1 = 2^b := by
        rw [← hp1]
        linarith
      rw [← geom_sum_mul, ← hp1] at h3
      
      have : Odd (∑ i ∈ Finset.range a, p ^ i) := by
        have : a = (a-1) + 1 := by omega
        rw [this, Finset.sum_range_succ']
        
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

        have : (∑ i ∈ Finset.range (a - 1), 1) = (a-1) := by exact finset_sum_range_one_eq
        rw [this, hk]

        omega
      
      --have : (p - 1) ∣ p^a - 1^a := by exact nat_sub_dvd_pow_sub_pow p 1 a
      
      sorry
  · sorry
