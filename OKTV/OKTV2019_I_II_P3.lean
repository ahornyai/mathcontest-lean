import Mathlib.Tactic
/-
OKTV 2019/2020, I. kategória, II. forduló, 3. feladat:

Oldja meg a valós számok halmazán a következő egyenletet:
√(x^2 + x - 6) - √(-x^2 + 7*x - 10) = √(x^2 + 9*x - 22)
--------------------------------
igazoljuk, hogy az egyenlet egyetlen megoldása az x=2
https://www.oktatas.hu/pub_bin/dload/kozoktatas/tanulmanyi_versenyek/oktv/oktv2019_2020_2ford/mat1_javut2f_oktv_1920.pdf
hibás megoldókulcs!! (6) egyenlet x-13 helyett -x-3
-/
theorem oktv2019_i_ii_iii (x : ℝ) (h1 : x^2 + x - 6 ≥ 0) (h2 : -x^2 + 7*x - 10 ≥ 0)
  : √(x^2 + x - 6) - √(-x^2 + 7*x - 10) = √(x^2 + 9*x - 22) ↔ x=2 := by
  constructor
  · intro h
    by_contra! hx_neq_2
    have : 2 ≤ x := by nlinarith
    have : x ≤ 5 := by nlinarith

    have : x^2+x-6 = (x-2)*(x+3) := by ring_nf
    rw [this] at h

    have : -x^2 + 7*x - 10 = (x-2)*(-x+5) := by ring_nf
    rw [this] at h

    have : x^2 + 9*x - 22 = (x-2)*(x+11) := by ring_nf
    rw [this] at h

    have : √(x - 2) ≠ 0 := by
      by_contra!
      rw [Real.sqrt_eq_iff_eq_sq (by linarith) (by norm_num)] at this
      have : x=2 := by linarith
      contradiction

    repeat rw [Real.sqrt_mul'] at h
    rw [← mul_sub_left_distrib] at h
    rw [mul_right_inj' this] at h

    have h4 : √(x + 3) - √(-x + 5) ≥ 0 := by
      refine sub_nonneg_of_le ?_
      rw [Real.sqrt_le_sqrt_iff]
      all_goals linarith

    rw [← sq_eq_sq₀ h4 (by exact Real.sqrt_nonneg (x + 11))] at h
    rw [sub_pow_two] at h
    repeat rw [Real.sq_sqrt (by linarith)] at h

    have : 2 * √(x + 3) * √(-x + 5) = -3-x := by linarith

    have rhs_neg : -3-x < 0 := by linarith
    have lhs_nonneg : 2 * √(x + 3) * √(-x + 5) ≥ 0 := by
      refine mul_nonneg ?_ ?_
      refine mul_nonneg (by norm_num) ?_
      exact Real.sqrt_nonneg (x + 3)
      exact Real.sqrt_nonneg (-x + 5)

    all_goals linarith
  · intro h
    rw [h]
    norm_num
