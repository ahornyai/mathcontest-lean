import Mathlib.Tactic

/-
OKTV 2016/2017, III. kategória, I. forduló, 3. feladat:

Oldjuk meg a
16/3 * x^4 + 1/(6*x^2) = Real.sin (Real.pi*x)
egyenletet a valós számok halmazán.
--
bizonyítsuk be, hogy az egyetlen megoldás: x=1/2
-/
theorem oktv2016_iii_i_iii {x : ℝ} (hx_neq_0: x ≠ 0) : 16/3 * x^4 + 1/(6*x^2) = Real.sin (Real.pi*x) ↔ x=1/2 := by
  have hpid2_eq : Real.pi*(1/2) = Real.pi/2 := by ring_nf

  constructor
  · intro h
    have rhs_leq : Real.sin (Real.pi*x) ≤ 1 := by exact Real.sin_le_one (Real.pi * x)
    have rhs_geq : 16/3 * x^4 + 1/(6*x^2) ≥ 1 := by
      have h13_gt_0 : 0 ≤ (1/3 : ℝ) := by norm_num
      have h163x4_gt_0 : 0 ≤ 16/3*x^4 := by
        refine Left.mul_nonneg (by norm_num) ?_
        refine Even.pow_nonneg (by decide) x
      have h12x2_gt_0 : 0 ≤ 1/(12*x^2) := by
        refine one_div_nonneg.mpr ?_
        refine Left.mul_nonneg (by norm_num) ?_
        refine Even.pow_nonneg (by decide) x

      have amgm : (16/3*x^4)^(1/3 : ℝ) * (1/(12*x^2))^(1/3 : ℝ) * (1/(12*x^2))^(1/3 : ℝ) ≤ 1/3*(16/3*x^4) + 1/3*(1/(12*x^2)) + 1/3*(1/(12*x^2)) := by
        exact Real.geom_mean_le_arith_mean3_weighted h13_gt_0 h13_gt_0 h13_gt_0 h163x4_gt_0 h12x2_gt_0 h12x2_gt_0 (by norm_num)

      repeat rw [← Real.mul_rpow] at amgm

      have : 16 / 3 * x ^ 4 * (1 / (12 * x ^ 2)) * (1 / (12 * x ^ 2)) = 1/27 := by
        field_simp
        ring_nf
      rw [this] at amgm

      have : (1/27 : ℝ)^(1/3 : ℝ) = 1/3 := by
        refine (Real.eq_rpow_inv ?_ h13_gt_0 ?_).mp ?_
        all_goals norm_num
      rw [this] at amgm

      have : 0 < (3 : ℝ) := by norm_num
      rw [← mul_le_mul_right this] at amgm

      have : (1 / 3 * (16 / 3 * x ^ 4) + 1 / 3 * (1 / (12 * x ^ 2)) + 1 / 3 * (1 / (12 * x ^ 2))) * 3 = 16 / 3 * x ^ 4 + 1 / (6 * x ^ 2) := by
        field_simp
        ring_nf
      rw [this] at amgm

      linarith
      nlinarith
      exact h12x2_gt_0
      exact h163x4_gt_0
      exact h12x2_gt_0

    have : 6*x^2 ≠ 0 := by
      by_contra!
      have : x=0 := by nlinarith
      contradiction

    have lhs_eq_1 : 16/3 * x^4 + 1/(6*x^2) = 1 := by linarith
    have : 32*x^6 - 6*x^2 + 1 = 0 := by
      field_simp at lhs_eq_1
      linarith
    have : (2*x-1)^2 * (2*x+1)^2 * (2*x^2 + 1) = 0 := by linarith
    norm_num at this

    rcases this with this | h1
    · rcases this with h1 | h1
      · linarith
      · have : x=-1/2 := by linarith
        rw [this] at h

        norm_num at h
        rw [hpid2_eq] at h

        norm_num at h
    · nlinarith
  · intro h
    rw [h, hpid2_eq]
    norm_num
