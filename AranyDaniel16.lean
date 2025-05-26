import Mathlib.Tactic

/-
Arany Dániel 2016/2017 Haladók I. kategória II. forduló I. feladat

Melyek azok az (a, b) egész számpárok, amelyekre teljesül az alábbi egyenlőtlenség:
a^2 + 7*b^2 ≤ 4*a*b + 6*b
---------------------
Bizonyítsuk, hogy a megoldáshalmaz: (a,b) ∈ {(0, 0), (1, 1), (2, 1), (3, 1), (4, 2)}
-/
def SolutionSet : Set (ℤ × ℤ) := {(0, 0), (1, 1), (2, 1), (3, 1), (4, 2)}

theorem arany2019_advanced_i_ii_i (a b : ℤ) : a^2 + 7*b^2 ≤ 4*a*b + 6*b ↔ ⟨a, b⟩ ∈ SolutionSet := by
  unfold SolutionSet
  simp

  constructor
  · intro h
    have h1 : (a - 2*b)^2 + 3*(b-1)^2 ≤ 3 := by linarith
    
    have hub : (b - 1) ^ 2 ≤ 1 := by nlinarith
    have hlb : 0 ≤ (b-1)^2 := by exact sq_nonneg (b - 1)

    have : (b - 1) ^ 2 = 0 ∨ (b - 1) ^ 2 = 1 := by omega

    rcases this with h2 | h2
    · have : b=1 := by nlinarith
      rw [this] at h1
      norm_num at h1
      
      have : a < 4 := by nlinarith
      have : 0 < a := by nlinarith

      interval_cases a
      all_goals omega
    · have : (b-1)^2 - 1^2 = 0 := by linarith
      rw [sq_sub_sq] at this
      simp at this

      rcases this with h3 | h3
      · rw [h3] at h1
        norm_num at h1

        omega
      · have : b=2 := by linarith
        rw [this] at h1
        norm_num at h1

        omega
  · intro h
    rcases h with h | h | h | h | h
    all_goals
      obtain ⟨rfl, rfl⟩ := h
      decide
