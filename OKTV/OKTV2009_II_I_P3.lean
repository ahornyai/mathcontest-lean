import Mathlib.Tactic
/-
OKTV 2009/2010, II. kategória, I. forduló, 3. feladat:

Oldjuk meg a következő egyenletet:
11^x + 14^x = 25^x - 2*(sqrt(154))^x
----
bizonyítsuk be, hogy az egyetlen megoldás az x=2
-/
noncomputable def f (x : ℝ) : ℝ := ((√11)/5)^x + ((√14)/5)^x

theorem oktv2009_ii_i_iii (x : ℝ) : 11^x + 14^x = 25^x - 2*(√154)^x ↔ x=2 := by
  constructor
  · intro h

    have : √154 = √11 * √14 := by
      have : (154 : ℝ) = 11*14 := by norm_num
      rw [this, Real.sqrt_mul (by norm_num)]
    rw [this] at h

    have : (25^x : ℝ) = (5^x)^2 := by
      rw [Real.rpow_pow_comm]
      all_goals norm_num
    rw [this] at h

    have h : 11^x + 2*(√11 * √14)^x + 14^x = (5^x)^2 := by linarith

    have : ((√11)^x + (√14)^x)^2 = 11^x + 2*(√11 * √14)^x + 14^x := by
      rw [add_pow_two]
      repeat rw [Real.rpow_pow_comm]
      rw [Real.mul_rpow]
      all_goals norm_num
      ring_nf
    rw [← this] at h

    have : ((√11)^x + (√14)^x)^2 = (5^x)^2 ↔ (√11)^x + (√14)^x = 5^x := by
      have : (5^x : ℝ) ≥ 0 := by
        refine Real.rpow_nonneg ?_ x
        norm_num

      refine sq_eq_sq₀ ?_ this
      refine add_nonneg ?_ ?_
      all_goals exact Real.rpow_nonneg (by norm_num) x
    rw [this] at h

    have : (5^x : ℝ) ≠ 0 := by
      refine (Real.rpow_ne_zero ?_ ?_).mpr ?_
      norm_num
      by_contra!
      rw [this] at h
      norm_num at h
      norm_num
    rw [← div_eq_one_iff_eq this] at h

    have : ((√11)^x + (√14)^x) / (5^x : ℝ) = 1 ↔ (√11)^x/5^x + (√14)^x / (5^x : ℝ) = 1 := by ring_nf
    rw [this] at h
    repeat rw [← Real.div_rpow (by norm_num) (by norm_num)] at h

    have hstrict_anti: StrictAnti f := by
      unfold f
      refine StrictAnti.add ?_ ?_

      all_goals
        refine Real.strictAnti_rpow_of_base_lt_one (by norm_num) ?_
        refine (div_lt_one (by norm_num)).mpr ?_
        refine (Real.sqrt_lt' ?_).mpr ?_
        all_goals norm_num

    have : f x = f 2 := by
      unfold f
      rw [h, Real.div_rpow, Real.div_rpow]
      all_goals norm_num

    exact StrictAnti.injective hstrict_anti this
  · intro h
    rw [h]
    norm_num
