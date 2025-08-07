import Mathlib.Tactic
/-
OKTV 2014/2015, III. kategória, I. forduló, 1. feladat:

Mely 1-nél nagyobb egész számok lehetnek két egymást követő n^2 + 3 alakú szám közös osztói?
----
bizonyítsuk be, hogy az egyetlen megoldás az x=13, n=6
-/
theorem oktv2014_iii_i_i (x : ℤ) (hx_gt_1 : x > 1) : (∃n, (x ∣ n^2 + 3 ∧ x ∣ (n+1)^2 + 3)) ↔ x=13 := by
  constructor
  · intro h
    obtain ⟨n, h1, h2⟩ := h

    have hsub_dvd: x ∣ ((n+1)^2 + 3) - (n^2 + 3) := by exact Int.dvd_sub h2 h1
    have : ((n+1)^2 + 3) - (n^2 + 3) = 2*n+1 := by ring_nf
    rw [this] at hsub_dvd

    have h3 : x ∣ n*(2*n + 1) - 2*(n^2 + 3) := by
      refine Int.dvd_sub ?_ ?_
      exact Dvd.dvd.mul_left hsub_dvd n
      exact Dvd.dvd.mul_left h1 2
    have : n*(2*n + 1) - 2*(n^2 + 3) = n-6 := by ring_nf
    rw [this] at h3

    have h4 : x ∣ (2*n + 1) - 2*(n-6) := by
      refine Int.dvd_sub hsub_dvd ?_
      exact Dvd.dvd.mul_left h3 2
    have : (2*n + 1) - 2*(n-6) = 13 := by ring_nf
    rw [this] at h4

    obtain ⟨k, hk⟩ := h4
    have h13_prime : Nat.Prime 13 := by norm_num

    have hkx_prod_nonneg : x*k ≥ 0 := by
      rw [← hk]
      norm_num

    have x_nonneg : x ≥ 0 := by linarith
    have k_nonneg : k ≥ 0 := by
      refine nonneg_of_mul_nonneg_right hkx_prod_nonneg ?_
      linarith

    have x_nat : ∃ n : ℕ, x = n := ⟨Int.natAbs x, by rw [Int.natAbs_of_nonneg x_nonneg]⟩
    have k_nat : ∃ n : ℕ, k = n := ⟨Int.natAbs k, by rw [Int.natAbs_of_nonneg k_nonneg]⟩

    obtain ⟨xn, hxn⟩ := x_nat
    obtain ⟨kn, hkn⟩ := k_nat

    have hk_eq_one : k=1 := by
      by_contra!

      have : ¬ Nat.Prime 13 := by
        refine (Nat.not_prime_iff_exists_dvd_ne ?_).mpr ?_
        norm_num
        use kn

        constructor
        · use xn
          rw [hxn, hkn, Int.mul_comm] at hk
          norm_cast at hk
        · constructor
          · omega
          · by_contra!
            rw [this] at hkn
            rw [hkn] at hk
            norm_cast at hk
            have : x=1 := by linarith
            linarith

      contradiction

    rw [hk_eq_one] at hk
    norm_num at hk
    exact hk.symm
  · intro h
    use 6
    rw [h]
    norm_num
