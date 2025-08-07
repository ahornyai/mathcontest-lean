import Mathlib.Tactic

/-
Arany Dániel 2015/2016 Haladók I. kategória I. forduló V. feladat

Hány rendezett (x, y, z) valós számhármas megoldása van az alábbi egyenletrendszernek
x+y+z = 11
x^2 + 2*y^2 + 3*z^2 = 66
----------------------
Bizonyítsuk, hogy az egyetlen megoldás x=6 ∧ y=3 ∧ z=2
-/
theorem arany2015_advanced_i_i_v (x y z : ℝ) : (x+y+z = 11 ∧ x^2 + 2*y^2 + 3*z^2 = 66) ↔ x=6 ∧ y=3 ∧ z=2 := by
  constructor
  · intro h
    obtain ⟨h1, h2⟩ := h

    have hz : z = 11 - x - y := by linarith

    have h3 : 4*(x*x) + (6*(y-11))*x + (5*y^2 - 66*y + 297) = 0 := by
      rw [hz] at h2
      nlinarith

    by_cases hy: y=3
    · rw [hy] at h3
      have hx : x=6 := by nlinarith
      have hz : z=2 := by linarith

      exact ⟨hx, hy, hz⟩
    · have : ∀s : ℝ, discrim 4 (6*(y-11)) (5*y^2 - 66*y + 297) ≠ s^2 := by
        intro s h
        unfold discrim at h

        have : y = 3 := by nlinarith

        contradiction

      apply quadratic_ne_zero_of_discrim_ne_sq at this
      specialize this x
      contradiction
  · intro h
    obtain ⟨rfl, rfl ,rfl⟩ := h
    norm_num
