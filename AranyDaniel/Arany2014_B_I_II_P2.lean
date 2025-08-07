import Mathlib.Tactic

/-
Arany Dániel 2014/2015 Kezdők I. kategória II. forduló II. feladat

Mely x és y valós számokra teljesül a következő egyenlőtlenség:
x + y + x*y ≥ x^2 + y^2 + 1
----------------------
Bizonyítsuk, hogy az egyetlen megoldás: x=1 ∧ y=1
-/
theorem arany2014_beginner_i_ii_i (x y : ℝ) : x + y + x*y ≥ x^2 + y^2 + 1 ↔ x=1 ∧ y=1 := by
  constructor
  · intro h

    have h1 : (x-y)^2 + (x-1)^2 + (y-1)^2 ≤ 0 := by linarith
    have hx_eq_y : x = y := by nlinarith

    rw [hx_eq_y] at h1

    have hx_eq : x=1 := by nlinarith
    have hy_eq : y=1 := by linarith

    exact ⟨hx_eq, hy_eq⟩
  · intro h
    obtain ⟨rfl, rfl⟩ := h
    norm_num
