import Mathlib.Tactic

/-
Arany Dániel 2020/2021 Haladók I. kategória I. forduló 1. feladat

Keressük meg mindazokat a p ∈ ℕ prímszámokat, amelyekre p^3 + p^2 + 11*p + 2 is prím.
------------
Bizonyítsuk, hogy az egyetlen ilyen prím a p=3
-/
theorem arany2020_advanced_i_i_i (p : ℕ) (hp : Nat.Prime p) : Nat.Prime (p^3 + p^2 + 11*p + 2) ↔ p=3 := by
  constructor
  · intro h

    have hp_geq_3 : p ≥ 3 := by
      by_contra!
      interval_cases p
      all_goals trivial

    mod_cases h1 : p%3
    · have : 3 ∣ p := by exact Nat.dvd_of_mod_eq_zero h1
      obtain ⟨k, hk⟩ := this

      rw [hk] at hp

      have : k = 1 := by
        by_contra!
        have hp_contra : ¬ Nat.Prime (3*k) := by
          refine Nat.not_prime_mul ?_ this
          exact Nat.add_one_add_one_ne_one

        contradiction

      rw [this] at hk
      exact hk
    · unfold Nat.ModEq at h1
      have : 3 ∣ p-1 := by refine (Nat.modEq_iff_dvd' (by linarith)).mp (id (Eq.symm h1))
      obtain ⟨k, hk⟩ := this

      have : p = 3*k+1 := by omega

      have h_contra : ¬ Nat.Prime (p ^ 3 + p ^ 2 + 11 * p + 2) := by
        rw [this]

        have : (3 * k + 1) ^ 3 + (3 * k + 1) ^ 2 + 11 * (3 * k + 1) + 2 = 3*(9*k^3 + 12*k^2 + 16*k + 5) := by ring_nf
        rw [this]

        exact Mathlib.Meta.NormNum.not_prime_mul_of_ble 3 (9 * k ^ 3 + 12 * k ^ 2 + 16 * k + 5) (3 * (9 * k ^ 3 + 12 * k ^ 2 + 16 * k + 5)) rfl rfl rfl

      contradiction
    · unfold Nat.ModEq at h1
      have : 3 ∣ p-2 := by refine (Nat.modEq_iff_dvd' (by linarith)).mp (id (Eq.symm h1))
      obtain ⟨k, hk⟩ := this

      have : p = 3*k+2 := by omega

      have h_contra : ¬ Nat.Prime (p ^ 3 + p ^ 2 + 11 * p + 2) := by
        rw [this]

        have : (3 * k + 2) ^ 3 + (3 * k + 2) ^ 2 + 11 * (3 * k + 2) + 2 = 3*(9*k^3 + 21*k^2 + 27*k + 12) := by ring_nf
        rw [this]

        exact Mathlib.Meta.NormNum.not_prime_mul_of_ble 3 (9 * k ^ 3 + 21 * k ^ 2 + 27 * k + 12) (3 * (9 * k ^ 3 + 21 * k ^ 2 + 27 * k + 12)) rfl rfl rfl

      contradiction
  · intro h
    rw [h]
    decide
