import Mathlib.Tactic
/-
OKTV 2020/2021, II. kategória, III. forduló, 1. feladat:

Hány olyan pozitív egész szám van, amely nem eleme az
f(x) = sqrt(x^3 − x^2 − 2*x)
függvény értelmezési tartományának?
----------
mivel az értelmezési tartománya a gyökfüggvénynek x^3 − x^2 − 2*x ≥ 0
ezért a x^3 - x^2 - 2*x < 0 egyenlőtlenséget kell megoldanunk
-/
theorem oktv2020_ii_iii_i (x : ℤ) (hxpos : x > 0) : x^3 - x^2 - 2*x < 0 ↔ x =1 := by
  constructor
  all_goals intro; nlinarith
