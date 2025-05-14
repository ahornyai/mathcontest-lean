import Mathlib.Tactic
/-
OKTV 2017/2018, II. kategória, I. forduló, 3. feladat:

Oldjuk meg a valós számok körében az alábbi egyenletet:
√(2 + 4*x − 2*x^2) + √(6 + 6*x − 3*x^2) = x^2 − 2*x + 6
----
bizonyítsuk be, hogy az egyetlen megoldás az x=1
-/
theorem oktv_2017_ii_iii (x : ℝ) : √(2 + 4*x - 2*x^2) + √(6 + 6*x - 3*x^2) = x^2 - 2*x + 6 ↔ x=1 := by
  constructor
  · intro h
    have : 2+4*x-2*x^2=2*(2-(x-1)^2) := by ring
    rw [this] at h

    have : 6+6*x-3*x^2=3*(3-(x-1)^2) := by ring
    rw [this] at h

    have lhs_max : √(2*(2-(x-1)^2)) + √(3*(3-(x-1)^2)) ≤ 5 := by
      have : √(2*(2-(x-1)^2)) ≤ 2 := by
        rw [Real.sqrt_le_left ?_]
        nlinarith
        norm_num

      have : √(3*(3-(x-1)^2)) ≤ 3 := by
        rw [Real.sqrt_le_left ?_]
        nlinarith
        norm_num

      linarith

    have rhs_min : x^2 - 2*x + 6 ≥ 5 := by nlinarith

    have : (x-1)^2 = 0 := by linarith
    have : x-1=0 := by exact pow_eq_zero this

    linarith
  · intro h
    rw [h]
    norm_num

    have : √4 = 2 := by refine (Real.sqrt_eq_iff_mul_self_eq_of_pos (by norm_num)).mpr (by norm_num)
    rw [this]

    have : √9 = 3 := by refine (Real.sqrt_eq_iff_mul_self_eq_of_pos (by norm_num)).mpr (by norm_num)
    rw [this]

    norm_num
