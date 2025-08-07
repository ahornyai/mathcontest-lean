import Mathlib.Tactic

/-
OKTV 2013/2014, I. kategória, I. forduló, 2. feladat:

Melyek azok az n ∈ ℕ számok, amelyekre 2^(2*n+2) * 3^(2*n) + 1 prímszám?
--
bizonyítsuk be, hogy az egyetlen megoldás: n=0
-/
theorem oktv2013_i_i_ii (n : ℕ) :
  n=0 ↔ ∃ p, Nat.Prime p ∧ p = 2^(2*n+2) * 3^(2*n) + 1 := by
  constructor
  · intro h
    rw [h]
    norm_num
  · intro h
    by_cases h': n=0
    · rw [h']
    · exfalso
      obtain ⟨p, ⟨hp, h⟩⟩ := h

      have n_gt_0 : n > 0 := by exact Nat.zero_lt_of_ne_zero h'

      have : 2^(2*n+2) * 3^(2*n) + 1 = 4*6^(2*n) + 1 := by
        calc
          _ = 4*(2^(2*n) * 3^(2*n)) + 1 := by rw [Nat.pow_succ']; ring
          _ = 4*6^(2*n) + 1 := by rw [← Nat.mul_pow]

      rw [this] at h

      have p_div_5: 5 ∣ p := by
        refine Nat.dvd_of_mod_eq_zero ?_
        rw [h]
        rw [Nat.add_mod, Nat.mul_mod, Nat.pow_mod]
        norm_num

      obtain ⟨k, hk⟩ := p_div_5

      have hp_contra : ¬ Nat.Prime p := by
        refine Nat.not_prime_mul' hk.symm ?_ ?_
        norm_num
        by_contra!
        rw [this] at hk
        rw [hk] at h

        have : 6 ^ (2 * n) = 1 := by linarith
        rw [Nat.pow_eq_one] at this
        norm_num at this

        contradiction

      contradiction
