import Mathlib.Tactic
/-
OKTV 2004/2005, I. kategória, I. forduló, 4. feladat:

Van-e olyan n természetes szám, amelyre A = 3*n^2 + 3*n + 7 kifejezés egy természetes szám köbével egyenlő?
----------
Bizonyítsuk azt, hogy nincs
-/
theorem oktv_2018_iii_iii (n : ℕ) : ¬ ∃ m, m^3 = 3*n^2 + 3*n + 7 := by
  push_neg
  intro m

  have rhs_mod_3 : (3*n^2 + 3*n + 7) % 3 = 1 := by simp [Nat.add_mod]

  mod_cases h: m % 3
  · rw [Nat.ModEq] at h
    have : 3 ∣ m := by exact Nat.dvd_of_mod_eq_zero h
    obtain ⟨k, hk⟩ := this

    have lhs_mod_3 : m^3 % 3 = 0 := by simp [hk, Nat.add_mod, Nat.pow_mod]

    omega
  · rw [Nat.ModEq] at h
    have : m ≥ 1 := by
      refine Nat.one_le_iff_ne_zero.mpr ?_
      by_contra!
      rw [this] at h
      contradiction

    have : 3 ∣ m-1 := by exact (Nat.modEq_iff_dvd' this).mp (id (Eq.symm h))
    have : ∃k, m=3*k+1 := by
      use (m-1)/3
      omega

    obtain ⟨k, hk⟩ := this

    by_contra h
    rw [hk] at h

    have : n^2 + n + 2 = 9*k^3 + 9*k^2 + 3*k := by linarith

    have rhs_mod_3 : (9*k^3 + 9*k^2 + 3*k) % 3 = 0 := by omega
    have lhs_mod_3 : (n^2 + n + 2) % 3 ≠ 0 := by
      by_contra! h1

      mod_cases h: n%3
      · rw [Nat.ModEq] at h
        have : 3 ∣ n := by exact Nat.dvd_of_mod_eq_zero h

        obtain ⟨k, hk⟩ := this

        rw [hk] at h1
        simp [Nat.add_mod, Nat.pow_mod] at h1
      · rw [Nat.ModEq] at h
        have : n ≥ 1 := by
          refine Nat.one_le_iff_ne_zero.mpr ?_
          by_contra!
          rw [this] at h
          contradiction

        have : 3 ∣ n-1 := by exact (Nat.modEq_iff_dvd' this).mp (id (Eq.symm h))
        have : ∃k, n=3*k+1 := by
          use (n-1)/3
          omega

        obtain ⟨k, hk⟩ := this

        rw [hk] at h1
        simp [Nat.add_mod, Nat.pow_mod] at h1
      · rw [Nat.ModEq] at h
        have : n ≥ 2 := by
          by_contra!
          interval_cases n
          all_goals contradiction

        have : 3 ∣ n-2 := by exact (Nat.modEq_iff_dvd' this).mp (id (Eq.symm h))
        have : ∃k, n=3*k+2 := by
          use (n-2)/3
          omega

        obtain ⟨k, hk⟩ := this

        rw [hk] at h1
        simp [Nat.add_mod, Nat.pow_mod] at h1

    omega
  · rw [Nat.ModEq] at h
    have : m ≥ 2 := by
      by_contra!
      interval_cases m
      all_goals contradiction

    have : 3 ∣ m-2 := by exact (Nat.modEq_iff_dvd' this).mp (id (Eq.symm h))
    have : ∃k, m=3*k+2 := by
      use (m-2)/3
      omega

    obtain ⟨k, hk⟩ := this

    by_contra!
    rw [hk] at this

    have : 27*k^3 + 54*k^2 + 36*k + 8 = 3*n^2 + 3*n + 7 := by linarith
    have lhs_mod_3 : (27*k^3 + 54*k^2 + 36*k + 8) % 3 = 2 := by simp [Nat.add_mod, Nat.mul_mod]

    omega
