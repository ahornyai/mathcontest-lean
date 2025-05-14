import Mathlib.Tactic
import Mathlib.Algebra.Group.Even

/-
OKTV 2014/2015, I. kategória, I. forduló, 3. feladat:

Oldja meg az x^2 + y^2 - 8*z = 14 egyenletet az egész számok halmazán!
--
bizonyítsuk be, hogy nincs rá megoldás
-/

lemma square_mod4_neq_2 (a : ℤ) : a^2 % 4 ≠ 2 := by
  mod_cases a % 4
  · unfold Int.ModEq at H
    norm_num at H

    have : a^2 % 4 = 0 := by
      refine Int.emod_eq_zero_of_dvd ?_
      refine Dvd.dvd.pow H ?_
      norm_num

    omega
  · have : a^2 % 4 = 1^2 % 4 := by
      refine Int.ModEq.eq ?_
      exact Int.ModEq.pow 2 H

    omega
  · have : a^2 % 4 = 2^2 % 4 := by
      refine Int.ModEq.eq ?_
      exact Int.ModEq.pow 2 H

    omega
  · have : a^2 % 4 = 3^2 % 4 := by
      refine Int.ModEq.eq ?_
      exact Int.ModEq.pow 2 H

    omega

theorem oktv_2014_i_3 (x y z : ℤ) : x^2 + y^2 - 8*z ≠ 14 := by
  by_contra! h
  mod_cases x % 2
  · unfold Int.ModEq at H
    norm_num at H
    obtain ⟨k, hk⟩ := H

    rw[hk] at h
    have : (2 * k) ^ 2 + y ^ 2 - 8 * z = 14 ↔ 4 * k ^ 2 + y ^ 2 - 8 * z = 14 := by
      constructor
      · intro h
        linarith
      · omega

    rw [this] at h

    have lhs_mod_4 : (4 * k ^ 2 + y ^ 2 - 8 * z) % 4 = y ^ 2 % 4 := by omega
    have rhs_mod_4 : 14 % 4 = 2 := by omega

    have : (y^2) % 4 = 2 := by omega

    apply square_mod4_neq_2 at this
    exact this
  · unfold Int.ModEq at H
    norm_num at H
    have : ∃k : ℤ, x = 2 * k + 1 := by
      use (x-1)/2
      omega

    obtain ⟨k, hk⟩ := this

    rw [hk] at h
    have : (2 * k + 1) ^ 2 + y ^ 2 - 8 * z = 14 ↔ 4 *k^2 + 4*k + y^2 - 8*z = 13 := by
      constructor
      · intro h
        linarith
      · omega

    rw [this] at h

    mod_cases Hy : y % 2
    · unfold Int.ModEq at Hy
      norm_num at Hy
      obtain ⟨ky, hky⟩ := Hy

      rw [hky] at h

      have : (2 * ky) ^ 2 = 4 * ky^2 := by linarith

      have h8z_mod_2 : 8 * z % 2 = 0 := by omega
      have h4k_mod_2 : 4 * k % 2 = 0 := by omega
      have h4k2_mod_2 : 4 * k ^ 2 % 2 = 0 := by omega
      have h2ky_sq_mod_2 : 4 * ky^2 % 2 = 0 := by omega

      rw [this] at h

      omega
    · unfold Int.ModEq at Hy
      norm_num at Hy
      have : ∃m : ℤ, y = 2 * m + 1 := by
        use (y-1)/2
        omega

      obtain ⟨m, hm⟩ := this

      rw [hm] at h

      have : 4 * k ^ 2 + 4 * k + (2 * m + 1) ^ 2 - 8 * z = 13 ↔ 4*k^2 + 4*k + 1 + 4*m^2 + 4*m + 1 - 8*z = 14 := by
        constructor
        · intro h
          linarith
        · intro h
          linarith
      rw [this] at h

      have : 4*k^2 + 4*k + 1 + 4*m^2 + 4*m + 1 - 8*z = 14 ↔ k^2 + k + m^2 + m - 2*z = 3 := by omega
      rw [this] at h

      have : k^2 + k + m^2 + m - 2*z = 3 ↔ k*(k+1) + m*(m+1) - 2*z = 3 := by ring_nf
      rw [this] at h

      have k_consec_even : k*(k+1) % 2 = 0 := by
        refine Int.even_iff.mp ?_
        exact Int.even_mul_succ_self k

      have m_consec_even : m*(m+1) % 2 = 0 := by
        refine Int.even_iff.mp ?_
        exact Int.even_mul_succ_self m

      omega
