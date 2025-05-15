import Mathlib.Tactic
/-
OKTV 2009/2010, II. kategória, III. forduló, 1. feladat:

Az a, b és c valós paraméterekre teljesül, hogy 2*a^2 + 2 + 3*b + 6*c = 0.
Igazoljuk, hogy a (a^2 + 1)*x^2 + b*x + c = 0
egyenletnek van egynél kisebb, pozitív gyöke.
-/
theorem oktv_2009_ii_i : ∃ a b c x : ℝ, 0 < x ∧ x < 1 ∧ 2*a^2 + 2 + 3*b + 6*c = 0 ∧ (a^2 + 1)*x^2 + b*x + c = 0 := by
  sorry
