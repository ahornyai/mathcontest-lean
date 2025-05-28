import Mathlib.Tactic

/-
Arany Dániel 2013/2014 Kezdők I. kategória II. forduló II. feladat

Hány olyan pozitív egész szám van, amelynek szomszédjai prímszámok, és a szám nem
osztható 6-tal?
----------------------
Bizonyítsuk, hogy az egyetlen megoldás az n=4
-/
theorem arany2014_beginner_i_ii_ii (n : ℕ) : ((Nat.Prime (n-1)) ∧ (Nat.Prime (n+1)) ∧ (¬ 6 ∣ n)) ↔ n=4 := by
  constructor
  · intro h
    obtain ⟨h1, h2, h3⟩ := h

    mod_cases h4: n % 3
    · have : 3 ∣ n := by exact Nat.dvd_of_mod_eq_zero h4
      
      by_cases h5: Even n
      · obtain ⟨k, hk⟩ := h5
        omega
      · have hnm1_even : Even (n-1) := by
          refine Nat.Odd.sub_odd ?_ ?_
          exact Nat.not_even_iff_odd.mp h5
          exact Nat.odd_iff.mpr rfl
        have hnp1_even : Even (n+1) := by exact Nat.even_add_one.mpr h5

        obtain ⟨k, hk⟩ := hnm1_even
        have : n+1 = 2*(k+1) := by omega
        rw [this] at h2

        have h2_contra : ¬ Nat.Prime (2*(k+1)) := by
          refine Nat.not_prime_mul ?_ ?_
          decide
          omega
        
        contradiction
    · unfold Nat.ModEq at h4
      have : n ≥ 1 := by omega
      have : 3 ∣ n-1 := by exact (Nat.modEq_iff_dvd' this).mp (id (Eq.symm h4))
      obtain ⟨k, hk⟩ := this

      rw [hk] at h1

      have : k=1 := by
        by_contra!
        have h1_contra : ¬ Nat.Prime (3*k) := by exact Nat.not_prime_mul (by decide) this
        contradiction
      
      omega
    · unfold Nat.ModEq at h4
      have : n ≥ 2 := by
        by_contra!
        interval_cases n <;> trivial
      have : 3 ∣ n-2 := by exact (Nat.modEq_iff_dvd' this).mp (id (Eq.symm h4))
      
      obtain ⟨k, hk⟩ := this
      have hk : n=3*k+2 := by omega

      have : 3 * k + 2 + 1 = 3*(k+1) := by ring
      
      rw [hk, this] at h2

      have : k=0 := by
        by_contra!
        have h2_contra : ¬ Nat.Prime (3*(k+1)) := by
          refine Nat.not_prime_mul ?_ ?_
          decide
          omega
        contradiction
      
      rw [this] at hk
      rw [hk] at h1
      norm_num at h1
  · intro h
    rw [h]
    norm_num
