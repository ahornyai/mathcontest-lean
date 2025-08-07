import Mathlib.Tactic

/-
OKTV 2016/2017, III. kategória, III. forduló, 3. feladat:

Mutassuk meg, hogy minden k > 1 egész számhoz van olyan k^2-nél kisebb m pozitív egész,
amelyre 2^m − m osztható k-val.
-/
theorem oktv2016_iii_iii_iii (k : ℕ) (hk_gt_1 : k > 1) : ∃ m, m < k^2 ∧ 0 < m ∧ k ∣ 2^m - m := by
  sorry
