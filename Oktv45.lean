import Mathlib.Tactic
/-
OKTV 2017/2018, I. kategória, I. forduló, 2. feladat:

Oldja meg a valós számpárok halmazán az
x/y - 1 = 1 - y/x
x^5 + y^5 + x^2 + y^2 = 0
egyenletrendszert.
--------------------------------
Bizonyítsuk be, hogy az egyetlen megoldás az x=-1 y=-1
-/
theorem oktv_2017_i_ii (x y : ℝ) (hx_neq_0 : x ≠ 0) (hy_neq_0 : y ≠ 0) : (x/y - 1 = 1 - y/x ∧ x^5 + y^5 + x^2 + y^2 = 0) ↔ (x=-1 ∧ y=-1) := by
  constructor
  · intro h
    obtain ⟨h1, h2⟩ := h

    have : x*y ≠ 0 := by exact (mul_ne_zero_iff_right hy_neq_0).mpr hx_neq_0

    have hx_eq_y : x=y := by
      rw [← mul_left_inj' this] at h1
      field_simp at h1

      rcases h1 with h3 | h3
      · exact h3
      · have : x-y=0 := by exact (mul_eq_zero_iff_right this).mp h3
        linarith

    rw [← hx_eq_y] at h2

    have : x^2*(x^3 + 1) = 0 := by linarith
    have : x^2 = 0 ∨ x^3+1 = 0 := by exact mul_eq_zero.mp this

    rcases this with h3 | h3
    · have : x=0 := by exact pow_eq_zero h3
      contradiction
    · have : (x+1)*(x^2 - x + 1) = 0 := by linarith
      have : x+1=0 ∨ x^2 - x + 1=0 := by exact mul_eq_zero.mp this

      rcases this with h4 | h4
      · have : x=-1 := by linarith
        rw [← hx_eq_y, this]
        norm_num
      · nlinarith
  · intro h
    obtain ⟨rfl, rfl⟩ := h
    norm_num
