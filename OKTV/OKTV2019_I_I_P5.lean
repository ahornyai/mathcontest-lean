import Mathlib.Tactic
/-
OKTV 2019/2020, I. kategória, I. forduló, 5. feladat:

Oldja meg a valós számhármasok halmazán az
x^2 + y^2 + z^2 + 1/(z^2) = 15
2*x+3*y=13
egyenletrendszert.
--------------------------------
igazoljuk, hogy az egyenletrendszer megoldásai: (x,y,z) ∈ {(2, 3, -1), (2, 3, 1)}
-/
def SolutionSet : Set (ℝ × ℝ × ℝ) := {(2, 3, -1), (2, 3, 1)}

theorem oktv2019_i_i_v (x y z : ℝ) (hz_sq_neq_0 : z^2 ≠ 0) : (x^2 + y^2 + z^2 + (1/(z^2)) = 15 ∧ 2*x+3*y=13) ↔ ⟨x, y, z⟩ ∈ SolutionSet := by
  unfold SolutionSet
  constructor
  · intro h
    obtain ⟨h1, h2⟩ := h

    have z_neq_0 : z ≠ 0 := by exact right_ne_zero_of_mul hz_sq_neq_0

    have : (x^2 - 2*x*2 + 2^2) + (y^2 - 2*y*3 + 3^2) + (z^2 - 2*z*(1/z) + (1/z)^2) = 0 := by
      have : z*(1/z) = 1 := by exact mul_one_div_cancel z_neq_0
      rw [div_pow 1 z 2]
      linarith
    repeat rw [← sub_pow_two] at this

    have hx : x=2 := by nlinarith
    have hy : y=3 := by nlinarith
    have h3 : z*(z-1/z)=(z+1)*(z-1) := by
      rw [mul_sub_left_distrib]
      rw [mul_one_div_cancel z_neq_0]
      rw [← pow_two z]
      rw [← one_pow 2]
      rw [sq_sub_sq]
      norm_num
    have : z*(z-1/z) = 0 := by nlinarith
    rw [h3] at this

    have : z+1=0 ∨ z-1=0 := by exact mul_eq_zero.mp this
    rcases this with h4 | h4
    · have hz : z=-1 := by linarith
      rw [hx, hy, hz]
      norm_num
    · have hz : z=1 := by linarith
      rw [hx, hy, hz]
      norm_num
  · intro h
    simp at h

    rcases h with h1 | h1
    all_goals
      obtain ⟨rfl, rfl, rfl⟩ := h1
      norm_num
