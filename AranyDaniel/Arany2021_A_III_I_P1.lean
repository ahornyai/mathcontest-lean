import Mathlib.Tactic

/-
Arany Dániel 2021/2022 Haladók III. kategória I. forduló 1. feladat

Oldjuk meg az alábbi egyenletet a valós számok halmazán!
√(2-x) + (x^2)/(√(2-x)) + x^2 = 1/√(2-x) + (√(2-x))/(x^2) + 1/(x^2)
-------------------
bizonyítsuk, hogy a megoldáshalmaz: x ∈ {-1, 1}
-/
theorem arany2021_advanced_iii_i_i (x : ℝ) (hx_neq_0 : x ≠ 0) (hx_neq_2 : x ≠ 2) (h2x_geq_0 : 2-x ≥ 0)
  : √(2-x) + (x^2)/(√(2-x)) + x^2 = 1/√(2-x) + (√(2-x))/(x^2) + 1/(x^2) ↔ x=-1 ∨ x=1 := by
  constructor
  · intro h

    let a := √(2-x)
    let b := 1/x^2
    let c := 1/(a*b)

    have ha_neq_0 : a ≠ 0 := by
      unfold a
      by_contra!
      have : 2-x = 0^2 := by
        refine (Real.sqrt_eq_iff_eq_sq ?_ ?_).mp this
        exact h2x_geq_0
        norm_num
      have : x=2 := by linarith

      contradiction

    have h1 : a + c + 1/b = 1/a + 1/c + b := by
      unfold c a b
      field_simp at *

      exact h

    have habc_eq : a*b*c = 1 := by
      unfold c a b
      field_simp

    have habc_neq_0 : a*b*c ≠ 0 := by
      rw [habc_eq]
      norm_num

    have : a + c + a*c + 1 = b*c + a*b + b + a*b*c := by
      rw [habc_eq]

      have : a + c + a*c = b*c + a*b + b := by
        rw [← mul_left_inj' habc_neq_0] at h1
        field_simp at h1
        rw [habc_eq] at h1
        norm_num at h1

        have : b * (a * c) = a*b*c := by ring
        rw [this, habc_eq] at h1

        have : ((a + c) * b + 1) * (a * c) = (a+c)*(a*b*c) + a*c := by ring
        rw [this, habc_eq] at h1

        linarith

      linarith

    have : (b-1)*(a+1)*(c+1) = 0 := by linarith
    simp at this

    rcases this with h2 | h2
    · rcases h2 with h2 | h2
      · unfold b at h2
        field_simp at h2

        rw [← one_pow 2, sq_sub_sq] at h2

        simp at h2

        rcases h2 with h2 | h2
        · have : x=-1 := by linarith
          exact Or.inl this
        · have : x=1 := by linarith
          exact Or.inr this
      · have : a ≥ 0 := by
          unfold a
          exact Real.sqrt_nonneg (2 - x)

        linarith
    · have : c > 0 := by
        unfold c a b
        refine one_div_pos.mpr ?_
        refine Left.mul_pos ?_ ?_
        unfold a at ha_neq_0
        have : √(2-x) ≥ 0 := by exact Real.sqrt_nonneg (2 - x)

        exact lt_of_le_of_ne this (id (Ne.symm ha_neq_0))
        refine one_div_pos.mpr ?_
        exact pow_two_pos_of_ne_zero hx_neq_0

      linarith
  · intro h
    rcases h with h | h
    all_goals
      rw [h]
      norm_num
    ring
