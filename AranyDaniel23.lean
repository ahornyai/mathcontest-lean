import Mathlib.Tactic

/-
Arany Dániel 2013/2014 Kezdők II. kategória, III. forduló III. feladat

Határozzuk meg az összes olyan p prímszámot, melyekre az
x^4 + 4 = p*y^4
egyenlet megoldható az egész számok körében
----------------------
Bizonyítsuk, hogy a megoldáshalmaz: (p, x, y) ∈ {(5, 1, 1), (5, 1, -1), (5, -1, 1), (5, -1, -1)}
-/
def SolutionSet : Set (ℤ × ℤ × ℤ) := {(5, 1, 1), (5, 1, -1), (5, -1, 1), (5, -1, -1)}

lemma eq_not_solvable_if_both_even {p x y : ℤ} (hp : Prime p) (hx_even : 2 ∣ x) (hy_even : 2 ∣ y) : x^4 + 4 ≠ p*y^4 := by
  intro h
  
  have h2 : 16 ∣ p*y^4 := by
    obtain ⟨k, hk⟩ := hy_even

    have : p * (2 * k) ^ 4 = 16*(p*k^4) := by ring
    rw [hk, this]

    exact Int.dvd_mul_right 16 (p * k ^ 4)
  
  have h2_contra : ¬ 16 ∣ p*y^4 := by
    by_contra! h3
    obtain ⟨k, hk⟩ := hx_even
    have : (2 * k) ^ 4 = 16*(k^4) := by ring

    rw [← h, hk, this] at h3

    omega
    
  contradiction

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

theorem arany2014_beginner_ii_iii_iii (p x y : ℤ) (hp : Prime p) (hp_pos : p > 0) : x^4 + 4 = p*y^4 ↔ ⟨p, x, y⟩ ∈ SolutionSet := by
  unfold SolutionSet
  simp
  
  constructor
  · intro h

    have : ∃n : ℕ, p=n := by exact Int.eq_ofNat_of_zero_le (by linarith)
    obtain ⟨pn, hpn⟩ := this

    have hpn_prime : Nat.Prime pn := by
      refine Nat.prime_iff_prime_int.mpr ?_
      rw [← hpn]
      exact hp
    
    by_cases h1: p=2
    · have hrhs_even : 2 ∣ p*y^4 := by
        rw [h1]
        exact Int.dvd_mul_right 2 (y ^ 4)
      
      have hx_even : 2 ∣ x^4 := by omega
      rw [Prime.dvd_pow_iff_dvd (by exact Int.prime_two) (by norm_num)] at hx_even

      have hy_even : 2 ∣ y := by
        have hlhs_div_4 : 4 ∣ x^4 + 4 := by
          obtain ⟨k, hk⟩ := hx_even
          rw [hk]
          
          refine (Int.dvd_add_right ?_).mpr ?_
          have : (2*k)^4 = 4*(4*k^4) := by ring
          rw [this]
          exact Int.dvd_mul_right 4 (4 * k ^ 4)
          exact Int.dvd_of_emod_eq_zero rfl
        
        obtain ⟨k, hk⟩ := hlhs_div_4
        rw [h1, hk] at h
        
        have : 2 ∣ y^4 := by omega
        rw [Prime.dvd_pow_iff_dvd (by exact Int.prime_two) (by norm_num)] at this

        exact this
      
      have : x ^ 4 + 4 ≠ p * y ^ 4 := by exact eq_not_solvable_if_both_even hp hx_even hy_even

      contradiction
    · by_cases h2: x % 2 = 0
      · by_cases h3: y % 2 = 0
        · have : x ^ 4 + 4 ≠ p * y ^ 4 := by
            apply eq_not_solvable_if_both_even hp
            exact Int.dvd_of_emod_eq_zero h2
            exact Int.dvd_of_emod_eq_zero h3
          
          contradiction
        · have h4 : Even (x ^ 4 + 4) := by
            have : 2 ∣ x := by exact Int.dvd_of_emod_eq_zero h2
            obtain ⟨k, hk⟩ := this
            have : (2 * k) ^ 4 + 4 = 2*(8*k^4 + 2) := by ring
            
            rw [hk, this]
            exact even_two_mul (8 * k ^ 4 + 2)
          
          have h4_contra : ¬ Even (x^4 + 4) := by
            refine Int.not_even_iff_odd.mpr ?_
            rw [h]

            refine Odd.mul ?_ ?_
            rw [hpn]
            norm_num
            refine Nat.Prime.odd_of_ne_two hpn_prime (by omega)
            refine Odd.pow ?_
            refine Int.odd_iff.mpr ?_
            exact Int.emod_two_ne_zero.mp h3
          
          contradiction
      · by_cases h3: y % 2 = 0
        · have h4 : Odd (x ^ 4 + 4) := by
            refine Odd.add_even ?_ ?_
            refine Odd.pow ?_
            refine Int.odd_iff.mpr ?_
            exact Int.emod_two_ne_zero.mp h2
            exact Int.even_iff.mpr rfl
          
          have h4_contra : ¬ Odd (x^4 + 4) := by
            refine Int.not_odd_iff_even.mpr ?_
            rw [h]

            have : 2 ∣ y := by exact Int.dvd_of_emod_eq_zero h3
            obtain ⟨k, hk⟩ := this
            have : p*(2 * k) ^ 4 = 2*(8*k^4*p) := by ring
            
            rw [hk, this]
            exact even_two_mul (8 * k ^ 4 * p)
          
          contradiction
        · have h5 : (x^2 - 2*x + 2)*(x^2 + 2*x + 2) = p*y^4 := by linarith
          
          have hfacts_coprime : IsCoprime (x^2 - 2*x + 2) (x^2 + 2*x + 2) := by
            refine Int.isCoprime_iff_gcd_eq_one.mpr ?_
            refine Int.gcd_eq_one_iff.mpr ?_
            intro c hc1 hc2

            have hc3 : c ∣ (x^2 + 2*x + 2) - (x^2 - 2*x + 2) := by exact Int.dvd_sub hc2 hc1
            have : (x^2 + 2*x + 2) - (x^2 - 2*x + 2) = 4*x := by ring
            rw [this] at hc3

            have h2ndivc : ¬ 2 ∣ c := by
              by_contra!
              have : 2 ∣ x ^ 2 - 2 * x + 2 := by exact Int.dvd_trans this hc1
              
              have h6 : Even (p*y^4) := by
                refine Int.even_iff.mpr ?_
                obtain ⟨k, hk⟩ := this

                rw [← h5, hk, mul_assoc]
                exact Int.mul_emod_right 2 (k * (x ^ 2 + 2 * x + 2))
              
              have h6_contra : ¬ Even (p*y^4) := by
                refine Int.not_even_iff_odd.mpr ?_
                refine Odd.mul ?_ ?_
                rw [hpn]
                norm_cast
                refine Nat.Prime.odd_of_ne_two hpn_prime ?_
                omega
                refine Odd.pow ?_
                refine Int.odd_iff.mpr ?_
                exact Int.emod_two_ne_zero.mp h3
              
              contradiction

            have : IsCoprime c 4 := by
              refine Int.isCoprime_iff_gcd_eq_one.mpr ?_
              refine Int.gcd_eq_one_iff.mpr ?_
              intro d hd1 hd2

              have hd2_is_coprime_2 : IsCoprime d 2 := by
                symm
                refine (Prime.coprime_iff_not_dvd ?_).mpr ?_
                exact Int.prime_two
                
                by_contra!
                obtain ⟨k, hk⟩ := this
                
                have h2div_c: 2 ∣ c := by
                  rw [hk] at hd1
                  exact dvd_of_mul_right_dvd hd1
                
                contradiction
              
              have : d ∣ 2 := by exact IsCoprime.dvd_of_dvd_mul_left hd2_is_coprime_2 hd2
              
              exact IsCoprime.dvd_of_dvd_mul_left hd2_is_coprime_2 this

            have : c ∣ x := by exact IsCoprime.dvd_of_dvd_mul_left this hc3

            have hc4 : c ∣ x^2 + 2*x := by
              refine Int.dvd_add ?_ ?_
              refine dvd_pow this (by decide)
              exact Dvd.dvd.mul_left this 2
            
            have : c ∣ 2 := by
              have : 2 = (x ^ 2 + 2 * x + 2) - (x^2 + 2*x) := by ring
              rw [this]
              exact Int.dvd_sub hc2 hc4

            have hc2_is_coprime_2 : IsCoprime c 2 := by
              symm
              refine (Prime.coprime_iff_not_dvd ?_).mpr ?_
              exact Int.prime_two
              exact h2ndivc
            
            exact IsCoprime.dvd_of_dvd_mul_left hc2_is_coprime_2 this

          have : p ∣ (x ^ 2 - 2 * x + 2) ∨ p ∣ (x ^ 2 + 2 * x + 2) := by
            refine Prime.dvd_or_dvd hp ?_
            exact Dvd.intro (y ^ 4) (id (Eq.symm h5))
          
          /- now use oktv20 style reasoning -/
          rcases this with h6 | h6
          · obtain ⟨k, hk⟩ := h6
            have : 0 ≤ x^2 - 2*x + 2 := by nlinarith
            
            rw [hk, mul_nonneg_iff_of_pos_left hp_pos] at this
            
            have : ∃n : ℕ, n=k := by exact CanLift.prf k this
            obtain ⟨kn, hkn⟩ := this

            have : ∃n : ℕ, n=(x^2 + 2*x + 2) := by exact CanLift.prf (x ^ 2 + 2 * x + 2) (by nlinarith)
            obtain ⟨mn, hmn⟩ := this

            have hkn_mn_sq : IsSquare (kn*mn) := by
              refine Int.isSquare_natCast_iff.mp ?_
              push_cast
              
              have : k* (x^2 + 2*x + 2) = y^4 := by nlinarith
              
              rw [hkn, hmn, this]
              refine Even.isSquare_pow (by decide) y
            
            have hkn_mn_coprime : Nat.Coprime kn mn := by
              refine Nat.isCoprime_iff_coprime.mp ?_
              rw [hkn, hmn]
              rw [hk] at hfacts_coprime

              symm
              exact IsCoprime.of_mul_right_right (id (IsCoprime.symm hfacts_coprime))
            
            have : IsSquare kn ∧ IsSquare mn := by exact exists_sq_factors_if_coprime hkn_mn_sq hkn_mn_coprime
            obtain ⟨kn_sq, mn_sq⟩ := this
            obtain ⟨r, hr⟩ := mn_sq

            have : r^2 - (x+1)^2 = 1 := by nlinarith
            rw [sq_sub_sq] at this

            have : (r + (x + 1) : ℤ) = 1 ∨ (r + (x + 1) : ℤ) = -1 := by exact Int.eq_one_or_neg_one_of_mul_eq_one this
            
            rcases this with h6 | h6
            · have : (r - (x + 1) : ℤ) = 1 := by nlinarith
              
              have : r=1 := by linarith
              have hx : x=-1 := by linarith
              rw [hx] at h
              
              have hpy_eq_5 : p*y^4 = 5 := by linarith
              have hy_le_2 : y < 2 := by
                by_contra!
                have : 2^4 ≤ y^4 := by exact pow_le_pow_left₀ (by decide) this 4
                nlinarith
              have hy_gt_m2 : -2 < y := by
                by_contra!
                sorry
              
              sorry
            · sorry
          · sorry
  · intro h
    rcases h with h | h | h | h
    all_goals
      obtain ⟨rfl, rfl, rfl⟩ := h
      norm_num
