import Mathlib.Tactic
import Mathlib.Algebra.Group.Even

/-
OKTV 2006/2007, I. kategória, II. forduló, 5. feladat:

Milyen pozitív p, q, r prímszámokra teljesül, hogy (7-p)*(3*q+r) + p*q*r = 0
--
bizonyítsuk be, hogy az egyetlen megoldás: (p,q,r) = (17, 5, 2)
-/
theorem oktv2006_i_ii_v (p q r : ℕ) (hp : Nat.Prime p) (hq : Nat.Prime q) (hr : Nat.Prime r) :
  p=17 ∧ q=5 ∧ r=2 ↔ ((7-p)*(3*q+r) + p*q*r : ℤ) = 0 := by
  constructor
  · intro h
    obtain ⟨rfl, rfl, rfl⟩ := h
    rfl
  · intro h

    have p_neq_0: p ≠ 0 := by exact Nat.Prime.ne_zero hp
    have q_neq_0: q ≠ 0 := by exact Nat.Prime.ne_zero hq
    have r_neq_0: r ≠ 0 := by exact Nat.Prime.ne_zero hr

    have p_gt_7 : p > 7 := by
      by_contra! p_leq_7
      norm_cast at h

      have right_add_pos: 0 < p*q*r := by
        refine Nat.zero_lt_of_ne_zero ?_
        refine mul_ne_zero ?_ r_neq_0
        refine mul_ne_zero ?_ q_neq_0
        exact p_neq_0

      have lhs_pos : (7 - p) * (3 * q + r) + p * q * r > 0 := by exact Nat.add_pos_right ((7 - p) * (3 * q + r)) right_add_pos
      have lhs_nonneg : (7 - p) * (3 * q + r) + p * q * r ≠ 0 := by exact Nat.not_eq_zero_of_lt lhs_pos

      contradiction

    by_cases hq2: q=2
    · rw[hq2] at h
      norm_num at h

      have : ((7 - p) * (6 + r) + p * 2 * r : ℤ) = 42 + 7*r - p*(6-r) := by ring

      rw[this] at h
      rw[Int.sub_eq_zero] at h

      have rhs_pos : (p*(6 - r) : ℤ) > 0 := by linarith
      have r_less_6 : (r:ℤ) < 6 := by exact Int.lt_of_sub_pos ((nsmul_pos_iff p_neq_0).mp rhs_pos)
      have r_pos : 0 < (r:ℤ) := by omega

      interval_cases r_val: (r: ℤ)
      · omega
      · have : (p: ℤ) = 14 := by linarith
        norm_cast at this
        rw[this] at hp
        contradiction
      · have : (p: ℤ) = 21 := by linarith
        norm_cast at this
        rw[this] at hp
        contradiction
      · have : (p: ℤ) = 35 := by linarith
        norm_cast at this
        rw[this] at hp
        contradiction
      · norm_num at h
        norm_cast at h
        rw[← h] at hp
        contradiction
    · by_cases hr2: r=2
      · rw[hr2] at h

        have : (2:ℤ) = (2:ℕ) := by exact rfl
        rw [← this] at h

        have : ((7 - p) * (3 * q + 2) + p*q*2 : ℤ) = (q+2)*(21-p)-28 := by ring
        rw[this] at h
        rw[Int.sub_eq_zero] at h

        have p_le_21 : p < 21 := by
          by_contra!
          have left_fact_pos : (q+2 : ℤ) > 0 := by exact Int.sign_eq_one_iff_pos.mp rfl
          have lhs_pos : ((q+2)*(21-p) : ℤ) > 0 := by linarith
          have : (21-p : ℤ) ≤ 0:= by
            refine Int.sub_nonpos_of_le ?_
            exact Int.toNat_le.mp this

          have lhs_neg : ((q+2)*(21-p) : ℤ) ≤ 0 := by exact Linarith.mul_nonpos this left_fact_pos

          exact Lean.Omega.Int.le_lt_asymm lhs_neg lhs_pos

        have p_cands: p ∈ ({11, 13, 17, 19} : Set ℕ) := by interval_cases h: p; all_goals trivial

        rcases p_cands with (rfl | rfl | rfl | rfl)
        · omega
        · omega
        · omega -- only solution p=17
        · norm_num at h
          have : q = 12 := by linarith
          rw[this] at hq
          contradiction
      · have odd_q : Odd q := by exact Nat.Prime.odd_of_ne_two hq hq2
        have odd_r : Odd r := by exact Nat.Prime.odd_of_ne_two hr hr2
        have odd_p : Odd p := by
          refine Nat.Prime.odd_of_ne_two hp ?_
          linarith

        have right_fact_even: Even (3 * q + r) := by
          refine Odd.add_odd ?_ odd_r
          refine Odd.mul ?_ odd_q
          exact Nat.odd_iff.mpr rfl

        have odd_pqr : Odd (p*q*r : ℤ) := by
          norm_cast
          refine Odd.mul ?_ odd_r
          exact Odd.mul odd_p odd_q

        have even_left_add: Even (((7 - p) * (3 * q + r) : ℤ)) := by
          norm_cast
          refine Even.mul_left ?_ (Int.subNatNat 7 p)
          norm_cast

        have odd_lhs : Odd ((7 - p) * (3 * q + r) + p*q*r : ℤ) := by exact Even.add_odd even_left_add odd_pqr

        have even_rhs : Even (0 : ℤ) := by exact Int.even_iff.mpr rfl
        have even_rhs_contra : Odd (0 : ℤ) := by
          rw [h] at odd_lhs
          exact odd_lhs

        contradiction
