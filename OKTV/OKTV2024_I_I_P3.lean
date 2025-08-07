import Mathlib.Tactic
/-
OKTV 2024/2025, I. kategória, I. forduló, 3. feladat:

Oldja meg az alábbi egyenletet a valós számok halmazán.
1/sqrt(10-x) - 1/sqrt(10+x) = 2
----
bizonyítsuk be, hogy az egyetlen megoldás a 4*sqrt(6)
-/
theorem oktv2024_i_i_iii (x : ℝ) (hx1 : 10 - x > 0) (hx2 : x + 10 > 0) : 1/(√(10-x)) - 1/(√(10+x)) = 2 ↔ x=4*√6 := by
  constructor
  · intro h
    have h2_neq : √(10 + x) ≠ 0 := by
      refine (Real.sqrt_ne_zero ?_).mpr ?_
      linarith
      linarith

    field_simp at h

    have rhs_nonneg : 2 * (√(10 - x) * √(10 + x)) ≥ 0 := by
      refine mul_nonneg (by norm_num) ?_
      exact mul_nonneg (by norm_num) (by norm_num)
    have lhs_nonneg : √(10 + x) - √(10 - x) ≥ 0 := by linarith

    have h10x_nonneg : 10+x ≥ 0 := by linarith

    have : √(10-x) ≤ √(10+x) := by linarith
    have hx_geq_0 : x ≥ 0 := by
      rw [Real.sqrt_le_sqrt_iff h10x_nonneg] at this
      linarith

    rw [← sq_eq_sq₀ lhs_nonneg rhs_nonneg] at h
    rw [sub_pow_two] at h
    repeat rw [Real.sq_sqrt (by linarith)] at h

    have : 2*√(10 + x) * √(10 - x) = 2*√(10^2-x^2) := by
      rw [mul_assoc, mul_right_inj_of_invertible 2]
      rw [← Real.sqrt_mul h10x_nonneg (10 - x)]
      rw [← sq_sub_sq 10 x]
    rw [this] at h

    have : √(10 - x) * √(10 + x) = √(10^2-x^2) := by
      rw [← Real.sqrt_mul (by linarith) (10 + x)]
      rw [mul_comm]
      rw [← sq_sub_sq 10 x]
    rw [this] at h
    rw [mul_pow 2 _ 2] at h

    have : 2*(√(10^2 - x^2))^2 + √(10^2 - x^2) - 10 = 0 := by linarith

    let y := √(10^2 - x^2)
    have : 2*y^2 + y - 10 = 0 := by linarith
    have : (y-2)*(y+2.5) = 0 := by linarith
    have : y-2=0 ∨ y+2.5=0 := by exact mul_eq_zero.mp this

    rcases this with h1 | h1
    · have : y=2 := by linarith
      unfold y at this

      have h_inside_geq_0 : 10 ^ 2 - x ^ 2 ≥ 0 := by
        refine sub_nonneg_of_le ?_
        refine sq_le_sq' ?_ ?_
        exact neg_le_iff_add_nonneg'.mpr h10x_nonneg
        linarith

      rw [Real.sqrt_eq_iff_eq_sq] at this
      have : x^2=96 := by linarith
      have : x=√96 ∨ x=-√96 := by
        refine sq_eq_sq_iff_eq_or_eq_neg.mp ?_
        rw [Real.sq_sqrt (by norm_num)]
        exact this

      rcases this with h2 | h2
      · have : (96 : ℝ) = 4^2*6 := by norm_num
        rw [this] at h2
        rw [Real.sqrt_mul' (4^2) (by norm_num)] at h2
        rw [Real.sqrt_sq (by norm_num)] at h2

        exact h2
      · rw [h2] at hx_geq_0
        norm_num at hx_geq_0
        have : ¬ (√96) ≤ 0 := by norm_num

        contradiction
      exact h_inside_geq_0
      norm_num
    · linarith
  · intro h
    have h2_neq : √(10 + x) ≠ 0 := by
      refine (Real.sqrt_ne_zero ?_).mpr ?_
      linarith
      linarith

    field_simp

    have : √(10 - x) * √(10 + x) = √(10^2-x^2) := by
      rw [← Real.sqrt_mul (by linarith) (10 + x)]
      rw [mul_comm]
      rw [← sq_sub_sq 10 x]

    rw [this]
    rw [← sq_eq_sq₀ ?_ ?_]
    rw [sub_pow_two]
    repeat rw [Real.sq_sqrt (by linarith)]
    rw [mul_pow 2 _ 2]

    rw [mul_comm] at this
    rw [mul_assoc, this]

    rw [h]
    ring_nf
    repeat rw [Real.sq_sqrt]
    norm_num

    have : √4 = 2 := by
      refine (Real.sqrt_eq_iff_mul_self_eq_of_pos ?_).mpr ?_
      repeat norm_num
    rw [this]
    repeat norm_num

    rw [h]
    rw [Real.sqrt_le_sqrt_iff ?_]
    norm_num
    refine le_add_of_le_of_nonneg ?_ ?_
    refine le_add_of_le_of_nonneg ?_ ?_
    repeat norm_num
    refine le_add_of_le_of_nonneg ?_ ?_
    repeat norm_num
