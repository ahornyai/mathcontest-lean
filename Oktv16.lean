import Mathlib.Tactic

/-
OKTV 2022/2023, I. kategória, I. forduló, 1. feladat:

Bizonyítsa be, hogy a 3^n - 2*n^2 - 1 kifejezés értéke
minden pozitív egész n szám esetén osztható 8-cal.
-/
theorem oktv_2022_i_i (n : ℕ) (hnpos : n > 0) : 8 ∣ (3^n - 2*n^2 - 1 : ℤ) := by
  mod_cases h: n%2
  · rw [Nat.ModEq] at h
    have : 2 ∣ n := by exact Nat.dvd_of_mod_eq_zero h

    obtain ⟨k, hk⟩ := this

    refine Int.dvd_sub_of_emod_eq ?_
    rw [hk, pow_mul]
    push_cast

    have : (2 * (2*k) ^ 2 : ℤ) = 8*k^2 := by ring
    rw [this]

    rw [Int.sub_emod]
    norm_num
    norm_cast

    rw [Nat.pow_mod]
    norm_num
  · rw [Nat.ModEq] at h
    norm_num at h

    have : 2 ∣ n-1 := by exact (Nat.modEq_iff_dvd' hnpos).mp (id (Eq.symm h))
    have : ∃ k : ℕ, n=2*k+1 := by
      use (n-1)/2
      omega

    obtain ⟨k, hk⟩ := this

    refine Int.dvd_sub_of_emod_eq ?_
    rw [hk, pow_succ, pow_mul]
    push_cast

    have : (2*(2*k + 1)^2 : ℤ) = (8*k^2 + 8*k + 2) := by ring
    rw [this]

    simp [Int.sub_emod, Int.add_emod]

    have : (9 ^ k * 3 % 8 % 8 - 3 : ℤ) = 0 := by
      refine Int.sub_eq_zero.mpr ?_
      norm_cast

      rw [Nat.mul_mod, Nat.pow_mod]
      norm_num

    omega
