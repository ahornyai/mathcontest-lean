import Mathlib.Tactic
/-
OKTV 2010/2011, II. kategória, I. forduló, 3. feladat:

Oldjuk meg a természetes számok körében:
3^(2*x-1) = x^(9-2*x) - 5
----------
Bizonyítsuk, hogy az egyetlen megoldás x=2
-/
theorem oktv2010_ii_i_iii (x : ℕ) : 3^(2*x - 1) = x^(9 - 2*x) - 5 ↔ x=2 := by
  constructor
  · intro h

    have rhs_pos : x^(9 - 2*x) - 5 > 0 := by
      rw [← h]
      exact Nat.pos_of_neZero (3 ^ (2 * x - 1))

    have x_pow_gt_5 : x^(9 - 2*x) > 5 := by exact Nat.lt_of_sub_pos rhs_pos

    have x_pos : x > 0 := by
      refine Nat.pos_of_ne_zero ?_
      by_contra!
      rw [this, Nat.zero_pow] at x_pow_gt_5
      exact Nat.not_succ_le_zero 5 x_pow_gt_5
      exact Nat.zero_lt_succ 8

    have : 9 - 2*x > 0 := by
      refine Nat.pos_of_ne_zero ?_
      by_contra!
      rw [this, Nat.pow_zero] at x_pow_gt_5
      contradiction

    have x_lt_5 : 5 > x := by omega

    interval_cases x
    all_goals omega
  · intro h
    rw[h]
    exact rfl
