import Mathlib.Tactic

/-
Arany Dániel 2022/2023 Haladók III. kategória I. forduló III. feladat

Határozzuk meg azokat a nemnegatív egész számokból álló (x; y) számpárokat, amelyekre
(x*y - 7)^2 = x^2 + y^2
---------------
bizonyítsuk, hogy a megoldáshalmaz: (x,y) ∈ {(4, 3), (3, 4), (7, 0), (0, 7)}
-/
def SolutionSet : Set (ℤ × ℤ) := {(4, 3), (3, 4), (7, 0), (0, 7)}

theorem eq_of_mul_eq_thirteen {x y : ℤ} (h : x * y = -13) :
    x = 1 ∧ y = -13 ∨ x = 13 ∧ y = -1 ∨ x = -1 ∧ y = 13 ∨ x = -13 ∧ y = 1 := by
  have h₁ : (x, y) ∈ Int.divisorsAntidiag (-13) := by simpa using h
  have h₂ : Int.divisorsAntidiag (-13) = {(1, -13), (13, -1), (-1, 13), (-13, 1)} := by rfl

  simpa [h₂] using h₁

theorem eq_of_mul_eq_twelve_nat {x y : ℕ} (h : x * y = 12) :
    x = 1 ∧ y = 12 ∨ x = 2 ∧ y = 6 ∨ x = 3 ∧ y = 4 ∨ x = 4 ∧ y = 3 ∨ x = 6 ∧ y = 2 ∨ x = 12 ∧ y = 1 := by
  have h₁ : (x, y) ∈ Nat.divisorsAntidiagonal 12 := by simpa using h
  have h₂ : Nat.divisorsAntidiagonal 12 = {(1, 12), (2, 6), (3, 4), (4, 3), (6, 2), (12, 1)} := by rfl

  simpa [h₂] using h₁

theorem arany2022_advanced_iii_i_iii (x y : ℤ) (hxnonneg : x ≥ 0) (hynonneg : y ≥ 0)
  : (x*y - 7)^2 = x^2 + y^2 ↔ (x, y) ∈ SolutionSet := by
  unfold SolutionSet
  simp

  constructor
  · intro h

    have h1 : (x*y-6)^2 - (x+y)^2 = -13 := by linarith
    rw [sq_sub_sq] at h1
    apply eq_of_mul_eq_thirteen at h1

    have xn_nat : ∃ xn:ℕ, xn=x := by exact CanLift.prf x hxnonneg
    have yn_nat : ∃ yn:ℕ, yn=y := by exact CanLift.prf y hynonneg

    obtain ⟨xn, hxn⟩ := xn_nat
    obtain ⟨yn, hyn⟩ := yn_nat

    rcases h1 with h2 | h2 | h2 | h2
    · obtain ⟨h1, h2⟩ := h2
      have : x+y = 7 := by linarith
      have : x*y = 0 := by linarith
      simp at this

      omega
    all_goals
      obtain ⟨h1, h2⟩ := h2
      have : x+y = 7 := by linarith
      have : x*y = 12 := by linarith

      rw [← hxn, ← hyn] at this h1 h2
      norm_cast at this
      apply eq_of_mul_eq_twelve_nat at this

      rcases this with h3 | h3 | h3 | h3 | h3 | h3
      all_goals
        obtain ⟨rfl, rfl⟩ := h3
        omega
  · intro h
    rcases h with h1 | h1 | h1 | h1
    all_goals
      obtain ⟨rfl, rfl⟩ := h1
      norm_num
