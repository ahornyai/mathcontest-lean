import Mathlib.Tactic

/-
Arany Dániel 2021/2022 Kezdők I. kategória III. forduló 1. feladat

Adjuk meg azokat a p, q pozitív prímszámokat és n pozitív egészt, amelyekre
n^2 + 1 = (p^2 + 1)*(q^2 + 1) 
-------------------
bizonyítsuk, hogy a megoldáshalmaz: (p, q, n) ∈ {(2,3,7), (3,2,7)}
-/
def SolutionSet : Set (ℕ × ℕ × ℕ) := {(2,3,7), (3,2,7)}

lemma solve_if_one_prime_eq_2 {p q n : ℕ} (hp : p = 2) (hq : Nat.Prime q) : n^2 + 1 = (p^2 + 1)*(q^2 + 1) ↔ q=3 ∧ n=7 := by
  constructor
  · intro h
    have h3 : n^2 - 2^2 = 5*q^2 := by
      rw [Nat.sub_eq_iff_eq_add ?_]
      rw [hp] at h
      linarith
      by_contra!
      interval_cases n^2
      all_goals nlinarith
    rw [Nat.sq_sub_sq] at h3
    
    by_cases h1: n-2=5
    · by_cases h2: n-2=q
      · have : q=5 := by linarith
        rw [hp, this] at h
        
        have : IsSquare 129 := by
          use n
          linarith
        
        have : ¬ IsSquare 129 := by decide

        contradiction
      · have hn_eq : n=7 := by omega
        have hq_eq : q=3 := by nlinarith

        exact ⟨hq_eq, hn_eq⟩
    · by_cases h2: n-2=q
      · have : n ≥ 2 := by
          by_contra!
          interval_cases n
          all_goals nlinarith
        have : n+2 = q+4 := by omega
        rw [this, h2] at h3
        
        have h4 : 5 * q ^ 2 - (q + 4) * q = 0 := by exact Eq.symm (Nat.eq_sub_of_add_eq' h3)
        
        have : 5 * q ^ 2 - (q + 4) * q = 5*q^2 - (q^2 + 4*q) := by ring_nf
        rw [this] at h4
        rw [Nat.sub_add_eq] at h4
        
        have : 5 * q ^ 2 - q ^ 2 - 4 * q = 4*q^2 - 4*q := by
          refine Eq.symm (Mathlib.Tactic.LinearCombination'.sub_pf ?_ rfl)
          refine Eq.symm (Nat.sub_eq_of_eq_add ?_)
          ring_nf
        rw [this] at h4
        
        have : q*(q - 1) = 0 := by
          rw [Nat.mul_sub_left_distrib]
          have : 4*(q^2-q) = 0 := by
            rw [Nat.mul_sub_left_distrib]
            exact h4
          have : q * q - q * 1 = q^2-q := by ring_nf
          
          linarith
        simp at this

        rcases this with h5 | h5
        · rw [h5] at hq
          trivial
        · have : q ≥ 2 := by exact Nat.Prime.two_le hq
          nlinarith
      · have hndivq : ¬ n-2 ∣ q := by
          by_contra!
          obtain ⟨k, hk⟩ := this
          rw [hk] at hq

          have : k ≠ 1 := by
            by_contra!
            rw [this] at hk
            omega
          
          have : ¬ Nat.Prime ((n - 2) * k) := by
            refine Nat.not_prime_mul ?_ this
            by_contra!
            sorry
          
          contradiction
        
        have hndiv5 : ¬ n-2 ∣ 5 := by sorry

        sorry
  · intro h
    obtain ⟨rfl, rfl⟩ := h
    rw [hp]
    norm_num

theorem arany2022_beginner_i_iii_i (p q n : ℕ) (hnpos : n > 0) (hp : Nat.Prime p) (hq : Nat.Prime q) 
  : n^2 + 1 = (p^2 + 1)*(q^2 + 1) ↔ (p, q, n) ∈ SolutionSet := by
  unfold SolutionSet
  simp

  constructor
  · intro h
    
    by_cases h1: p=2
    · by_cases h2: q=2
      · rw [h1, h2] at h
        have : IsSquare 24 := by
          use n
          linarith
        have : ¬ IsSquare 24 := by decide

        contradiction
      · sorry
    · by_cases h2: q=2
      · sorry
      · have hp_odd : Odd p := by exact Nat.Prime.odd_of_ne_two hp h1
        have hq_odd : Odd q := by exact Nat.Prime.odd_of_ne_two hq h2

        obtain ⟨x, hx⟩ := hp_odd
        obtain ⟨y, hy⟩ := hq_odd

        have hdiv4 : 4 ∣ n^2 + 1 := by
          rw [hx, hy] at h
          have : ((2 * x + 1) ^ 2 + 1) * ((2 * y + 1) ^ 2 + 1) = 4*((2*x^2 + 2*x + 1)*(2*y^2 + 2*y + 1)) := by ring
          rw [this] at h
          exact Dvd.intro ((2 * x ^ 2 + 2 * x + 1) * (2 * y ^ 2 + 2 * y + 1)) (id (Eq.symm h))
        
        have hdiv4_contra : ¬ 4 ∣ n^2 + 1 := by
          have hn_odd : Odd n := by
            have hlhs_even : Even (n^2 + 1) := by
              have : 2 ∣ n^2 + 1 := by
                have : 4=2*2 := by norm_num
                rw [this] at hdiv4
                exact dvd_of_mul_right_dvd hdiv4
              
              exact (even_iff_exists_two_nsmul (n ^ 2 + 1)).mpr this
            
            have : Odd (n^2) ↔ Even (n^2 + 1) := by
              refine (fun {m n} => Nat.odd_add.mp) ?_
              ring_nf
              refine Even.one_add ?_
              refine Even.mul_left ?_ (n ^ 2)
              exact Nat.even_iff.mpr rfl
            rw [← this] at hlhs_even
            
            exact Nat.Odd.of_mul_right hlhs_even

          obtain ⟨z, hz⟩ := hn_odd
          rw [hz]

          have : (2 * z + 1) ^ 2 + 1 = 4*(z^2 + z) + 2 := by ring
          rw [this]

          by_contra h1
          have : 4 ∣ 4 * (z ^ 2 + z) := by exact Nat.dvd_mul_right 4 (z ^ 2 + z)
          have : 4 ∣ 2 := by exact (Nat.dvd_add_iff_right this).mpr h1
          
          contradiction
        
        contradiction
  · intro h
    rcases h with h | h
    all_goals
      obtain ⟨rfl, rfl, rfl⟩ := h
      norm_num
