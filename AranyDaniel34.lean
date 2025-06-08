import Mathlib.Tactic

/-
Arany Dániel 1998/1999 Kezdők I. kategória I. forduló III. feladat

Bizonyítsa be, hogy három egymást követő pozitív egész szám szorzata nem lehet egy egész szám harmadik hatványa!
-/
theorem arany1999_beginner_i_i_iii (x y : ℕ) (hxpos : x > 0) : x*(x+1)*(x+2) ≠ y^3 := by
  by_contra!

  have lhs_lb : x*(x+1)*(x+2) > x^3 := by nlinarith
  have lhs_ub : x*(x+1)*(x+2) < (x+1)^3 := by nlinarith

  rw [this] at lhs_lb lhs_ub

  have : y^3 > x^3 ↔ y > x := by exact Nat.pow_lt_pow_iff_left (by norm_num)
  rw [this] at lhs_lb

  have : y^3 < (x+1)^3 ↔ y < x+1 := by exact Nat.pow_lt_pow_iff_left (by norm_num)
  rw [this] at lhs_ub

  omega
