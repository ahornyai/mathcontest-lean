import Mathlib.Tactic

/-
OKTV 2013/2014, I. kategória, I. forduló, 1. feladat:

Oldja meg a valós számok halmazán a 3*25^x - 16^x = 2*20^x egyenletet
--
bizonyítsuk be, hogy az egyetlen megoldás: x=0
-/
theorem oktv2013_i_i_i (x : ℝ) :
  x=0 ↔ (3*25^x - 16^x : ℝ) = 2*20^x := by
  constructor
  · intro h
    rw [h]
    norm_num
  · intro h

    by_cases h': x=0
    · exact h'
    · have : (3*25^x - 16^x : ℝ) = 3*(5^x)^2 - (4^x)^2 := by
        rw [Real.rpow_pow_comm]
        rw [Real.rpow_pow_comm]
        all_goals norm_num
      rw [this] at h

      have : (20^x : ℝ) = 4^x * 5^x := by
        rw [← Real.mul_rpow]
        all_goals norm_num
      rw [this] at h

      have : (3 * (5 ^ x) ^ 2 - (4 ^ x) ^ 2 : ℝ) = 2 * (4 ^ x * 5 ^ x)
        ↔ ((3 * (5 ^ x) ^ 2 - (4 ^ x) ^ 2)/(4 ^ x * 5 ^ x) : ℝ) = 2 := by
        field_simp
      rw[this] at h

      have h5_pow_x_neq_0 : (5^x : ℝ) ≠ 0 := by
        refine (Real.rpow_ne_zero ?_ ?_).mpr ?_
        norm_num
        exact h'
        norm_num

      have h4_pow_x_neq_0 : (4^x : ℝ) ≠ 0 := by
        refine (Real.rpow_ne_zero ?_ ?_).mpr ?_
        norm_num
        exact h'
        norm_num

      have : ((3*(5^x)^2 - (4^x)^2)/(4^x*5^x) : ℝ) = 3*((5^x)/(4^x)) - ((5^x)/(4^x))⁻¹ := by
        refine div_eq_of_eq_mul ?_ ?_
        exact (mul_ne_zero_iff_right h5_pow_x_neq_0).mpr h4_pow_x_neq_0
        field_simp
        ring
      rw [this] at h

      have : (5^x / 4^x : ℝ) = (5/4)^x := by
        rw [Real.div_rpow]
        all_goals norm_num
      rw [this] at h

      have : (3*(5/4)^x - ((5/4)^x)⁻¹ : ℝ) = 2 ↔ (3*((5/4)^x)^2-1 : ℝ) = 2*(5/4)^x := by
        constructor
        · intro h
          field_simp at h
          rw [pow_two ((5 / 4) ^ x)]
          linarith
        · intro h
          field_simp
          rw [pow_two ((5 / 4) ^ x)] at h
          linarith
      rw [this] at h

      have : (3*((5/4)^x)^2-1 : ℝ) = 2*(5/4)^x ↔ (3*((5/4)^x)^2 - 2*(5/4)^x - 1 : ℝ) = 0 := by
        constructor
        · intro h
          linarith
        · intro h
          linarith
      rw [this] at h

      have : (3*((5/4)^x)^2 - 2*(5/4)^x - 1 : ℝ) = ((5/4)^x - 1) * ((5/4)^x + 1/3) := by linarith
      rw [this] at h
      rw [mul_eq_zero] at h

      cases h with
      | inl r =>
        have hpow_eq_1 : ((5 / 4) ^ x : ℝ) = 1 := by linarith
        have : ((5 / 4) ^ x : ℝ) = 1 ↔ x=0 := by
          constructor
          · intro h

            have h_log : Real.log ((5 / 4) ^ x) = Real.log 1 := by
              rw [h]

            rw [Real.log_rpow] at h_log
            rw [Real.log_one] at h_log

            all_goals norm_num

            have : x=0 := by
              rw [mul_eq_zero] at h_log

              norm_num at h_log
              exact h_log

            exact this
          · intro h
            rw [h]
            norm_num

        rw [this] at hpow_eq_1
        exact hpow_eq_1
      | inr r =>
        exfalso
        have hpow_eq_m13 : ((5 / 4) ^ x : ℝ) = -1/3 := by linarith
        have h_nonneg : ¬ ((5 / 4) ^ x : ℝ) < 0 := by
          push_neg
          refine Real.rpow_nonneg ?_ x
          norm_num
        have h_neg : ((5 / 4) ^ x : ℝ) < 0 := by
          rw [hpow_eq_m13]
          norm_num

        contradiction
