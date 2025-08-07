import Mathlib.Tactic
/-
OKTV 2012/2013, I. kategória, II. forduló, 1. feladat:

Mely valós x y számpárokra teljesül a
36/√(x-2) + 4/√(y-1) = 28 - 4*√(x-2) - √(y-1)
egyenlőség?
--------------------------------
Bizonyítsuk be, hogy az egyetlen megoldás az x=11 y=5
-/
theorem oktv2012_i_ii_i (x y : ℝ) (hx_gt_2 : x > 2) (hy_gt_1 : y > 1) : (36/√(x-2) + 4/√(y-1) = 28 - 4*√(x-2) - √(y-1)) ↔ (x=11 ∧ y=5) := by
  constructor
  · intro h
    have hsqrtx_neq_0 : √(x-2) ≠ 0 := by exact (Real.sqrt_ne_zero (by linarith)).mpr (by linarith)
    have hsqrty_neq_0 : √(y-1) ≠ 0 := by exact (Real.sqrt_ne_zero (by linarith)).mpr (by linarith)

    let a := √(x-2)
    let b := √(y-1)

    have : (36/a - 24 + 4*a) + (4/b - 4 + b) = 0 := by linarith
    have h1 : ((6/√a)^2 - 2*(6/√a)*(2*√a) + (2*√a)^2) + ((2/√b)^2 - 2*(2/√b)*√b + (√b)^2) = 0 := by
      have ha_sqrt_neq_0 : √a ≠ 0 := by
        by_contra!
        unfold a at this
        rw [Real.sqrt_eq_zero] at this

        contradiction
        exact Real.sqrt_nonneg (x - 2)
      have : √a > 0 := by
        unfold a
        refine Real.sqrt_pos_of_pos ?_
        exact Real.sqrt_ne_zero'.mp ha_sqrt_neq_0

      rw [mul_pow]
      repeat rw [div_pow _ _ 2]
      repeat rw [Real.sq_sqrt]

      have : 2 * (6 / √a) * (2 * √a) = 24 := by
        field_simp
        ring
      rw [this]

      have : 2 * (2 / √b) * √b = 4 := by
        field_simp
        norm_num
      rw [this]

      linarith
      exact Real.sqrt_nonneg (y - 1)
      exact Real.sqrt_nonneg (x - 2)

    repeat rw [← sub_pow_two] at h1

    have ha_eq_3 : a=3 := by
      have : (6 / √a - 2 * √a) ^ 2 = 0 := by nlinarith
      rw [sq_eq_zero_iff] at this

      have : (√a)^2 = 3 := by
        field_simp at this
        linarith
      rw [Real.sq_sqrt] at this

      exact this
      exact Real.sqrt_nonneg (x - 2)

    have hb_eq_2 : b=2 := by
      have : (2 / √b - √b) ^ 2 = 0 := by nlinarith
      rw [sq_eq_zero_iff] at this
      field_simp at this
      linarith

    have hx_eq_11 : x=11 := by
      unfold a at ha_eq_3
      rw [← sq_eq_sq₀] at ha_eq_3
      rw [Real.sq_sqrt] at ha_eq_3

      all_goals linarith

    have hy_eq_5 : y=5 := by
      unfold b at hb_eq_2
      rw [← sq_eq_sq₀] at hb_eq_2
      rw [Real.sq_sqrt] at hb_eq_2

      all_goals linarith

    exact ⟨hx_eq_11, hy_eq_5⟩
  · intro h
    obtain ⟨rfl, rfl⟩ := h
    norm_num

    have : √9 = 3 := by exact (Real.sqrt_eq_iff_mul_self_eq_of_pos (by norm_num)).mpr (by norm_num)
    rw [this]

    have : √4 = 2 := by exact (Real.sqrt_eq_iff_mul_self_eq_of_pos (by norm_num)).mpr (by norm_num)
    rw [this]

    norm_num
