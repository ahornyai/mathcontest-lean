import Mathlib.Tactic

/-
Arany Dániel 2016/2017 Haladók II. kategória III. forduló III. feladat

Oldja meg a következő egyenletet a valós számok halmazán!
(3*x + 3)/√x = 4 + (x + 1)/√(x^2 - x + 1)
----------------------
Bizonyítsuk, hogy az egyetlen megoldás x=1
-/
lemma add_reciprocal_geq_2 {a : ℝ} (hapos : a > 0) : a + 1/a ≥ 2 := by
  field_simp
  rw [le_div_iff₀ hapos]

  refine two_mul_le_add_of_sq_eq_mul ?_ ?_ ?_
  exact mul_self_nonneg a
  norm_num
  ring

theorem arany2017_advanced_ii_iii_iii (x : ℝ) (hxpos : x > 0) : (3*x + 3)/√x = 4 + (x + 1)/√(x^2 - x + 1) ↔ x=1 := by
  constructor
  · intro h
    have hxsqrt_pos : √(x ^ 2 - x + 1) > 0 := by exact Real.sqrt_pos_of_pos (by nlinarith)

    have hx1_neq_0 : √x ≠ 0 := by exact Real.sqrt_ne_zero'.mpr hxpos
    have hx2_neq_0 : √(x ^ 2 - x + 1) ≠ 0 := by exact Ne.symm (ne_of_lt hxsqrt_pos)

    have : 3*(√x + 1/√x) = (3*x + 3)/√x := by
      field_simp
      exact mul_add_one 3 x

    have : (√x + 1 / √x) ≥ 2 := by
      apply add_reciprocal_geq_2
      exact Real.sqrt_pos_of_pos hxpos

    have h1 : 2 ≤ (x + 1) / √(x ^ 2 - x + 1) := by linarith
    rw [le_div_iff₀ hxsqrt_pos] at h1
    rw [← sq_le_sq₀ (by linarith) (by linarith), mul_pow, Real.sq_sqrt (by nlinarith)] at h1

    nlinarith
  · intro h
    rw [h]
    norm_num
