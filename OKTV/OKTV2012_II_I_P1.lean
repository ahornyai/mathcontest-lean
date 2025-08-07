import Mathlib.Tactic
/-
OKTV 2012/2013, II. kategória, I. forduló, 1. feladat:

Mely x és y valós számok elégítik ki a √x = 2 − y, √y = x − 2 egyenletrendszert?
----
bizonyítsuk be, hogy az egyetlen megoldás az (x,y)=((3+√5)/2, (3-√5)/2)
-/
theorem oktv2012_ii_i_i (x y : ℝ) (hx_nonneg : x ≥ 0) (hy_nonneg : y ≥ 0) : (√x = 2 - y ∧ √y = x - 2) ↔ (x=(3+√5)/2 ∧ y= (3-√5)/2) := by
  constructor
  · intro h
    obtain ⟨h1, h2⟩ := h

    have hx_geq_2 : x ≥ 2 := by
      have : √y ≥ 0 := by exact Real.sqrt_nonneg y
      linarith

    have h_add : √x + √y = x - y := by linarith
    have : x-y = (√x + √y)*(√x - √y) := by
      rw [← sq_sub_sq]
      rw [Real.sq_sqrt hx_nonneg]
      rw [Real.sq_sqrt hy_nonneg]
    rw [this] at h_add

    have h_sqrt_diff_nonneg : √x + √y ≠ 0 := by
      by_contra!
      have : √x ≤ 0 := by linarith
      rw [Real.sqrt_le_left (by norm_num)] at this

      have : x=0 := by linarith
      rw [this] at h2

      have : √y ≥ 0 := by linarith

      linarith
    rw [left_eq_mul₀ h_sqrt_diff_nonneg] at h_add

    have hsqrtx_eq : √x = 1 + √y := by linarith
    rw [hsqrtx_eq] at h1

    have : y + √y - 1 = 0 := by linarith
    have : (√y - (-1+√5)/2)*(√y - (-1-√5)/2) = 0 := by
      ring_nf
      repeat rw [Real.sq_sqrt (by linarith)]
      linarith

    have : √y - (-1+√5)/2 = 0 ∨ √y - (-1-√5)/2 = 0 := by exact mul_eq_zero.mp this

    rcases this with h3 | h3
    · have : √y = (-1 + √5) / 2 := by linarith
      rw [this] at hsqrtx_eq

      have hy_eq : y = (3 - √5) / 2 := by linarith
      have hx_eq : x = (3 + √5) / 2 := by linarith

      exact ⟨hx_eq, hy_eq⟩
    · have : √y ≥ 0 := by exact Real.sqrt_nonneg y
      have : √y = (-1 - √5) / 2 := by linarith

      have : (-1 - √5) / 2 < 0 := by
        refine div_neg_of_neg_of_pos ?_ ?_
        refine sub_neg.mpr ?_
        refine Real.lt_sqrt_of_sq_lt ?_
        all_goals norm_num

      linarith
  · intro h
    obtain ⟨rfl, rfl⟩ := h

    have : √5 ≥ 1 := by exact Real.one_le_sqrt.mpr (by norm_num)

    constructor
    · rw [Real.sqrt_eq_iff_eq_sq hx_nonneg]
      rw [sub_pow_two]
      rw [div_pow _ 2 2]
      rw [sub_pow_two]
      rw [Real.sq_sqrt (by norm_num)]
      linarith
      linarith
    · rw [Real.sqrt_eq_iff_eq_sq hy_nonneg]
      rw [sub_pow_two]
      rw [div_pow _ 2 2]
      rw [add_pow_two]
      rw [Real.sq_sqrt (by norm_num)]
      linarith
      linarith
