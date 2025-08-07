import Mathlib.Tactic

/-
Arany Dániel 2023/2024 Haladók II. kategória I. forduló II. feladat

Oldjuk meg a következő egyenletrendszert az egész számok halmazán
x^2-y^2-z^2=1
y+z-x=-3
-----
bizonyítsuk, hogy a megoldáshalmaz: (x,y,z) ∈ {(-9, -8, -4), (-9, -4, -8), (3, 2, -2), (3, -2, 2)}
-/
def SolutionSet : Set (ℤ × ℤ × ℤ) := {(-9, -8, -4), (-9, -4, -8), (3, 2, -2), (3, -2, 2)}

theorem eq_of_mul_eq_five {x y : ℤ} (h : x * y = 5) :
    x = 1 ∧ y = 5 ∨ x = 5 ∧ y = 1 ∨ x = -1 ∧ y = -5 ∨ x = -5 ∧ y = -1 := by
  have h₁ : (x, y) ∈ Int.divisorsAntidiag 5 := by simpa using h
  have h₂ : Int.divisorsAntidiag 5 = {(1, 5), (5, 1), (-1, -5), (-5, -1)} := by rfl
  simpa [h₂] using h₁

theorem arany2023_advanced_ii_i_ii {x y z : ℤ} : (x^2-y^2-z^2=1 ∧ y+z-x=-3) ↔ (x, y, z) ∈ SolutionSet := by
  unfold SolutionSet
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff]

  constructor
  · intro h
    obtain ⟨h1, h2⟩ := h

    have : x=y+z+3 := by linarith
    have : (z + 3)*(y + 3) = 5 := by
      rw [this] at h1
      linarith

    apply eq_of_mul_eq_five at this

    rcases this with h3 | h3 | h3 | h3
    · have hz : z=-2 := by linarith
      have hy : y=2 := by linarith
      have hx : x=3 := by linarith

      right; right; left
      simp
      exact ⟨hx, hy, hz⟩
    · have hz : z=2 := by linarith
      have hy : y=-2 := by linarith
      have hx : x=3 := by linarith

      right; right; right
      simp
      exact ⟨hx, hy, hz⟩
    · have hz : z=-4 := by linarith
      have hy : y=-8 := by linarith
      have hx : x=-9 := by linarith

      left
      simp
      exact ⟨hx, hy, hz⟩
    · have hz : z=-8 := by linarith
      have hy : y=-4 := by linarith
      have hx : x=-9 := by linarith

      right; left
      simp
      exact ⟨hx, hy, hz⟩
  · intro h

    rcases h with h1 | h1 | h1 | h1
    all_goals
      obtain ⟨rfl, rfl, rfl⟩ := h1
      norm_num
