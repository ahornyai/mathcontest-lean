import Mathlib.Tactic

/-
Arany Dániel 2023/2024 Haladók I. kategória I. forduló III. feladat

Oldjuk meg az alábbi egyenletet a valós számok halmazán.
x^4 - 11*x^2 + 25 = -6*x + 9
-----
bizonyítsuk, hogy a megoldáshalmaz: x ∈ {-1, 2, (-1+√33)/2, (-1-√33)/2}
-/
noncomputable def SolutionSet : Set ℝ := {-1, 2, (-1+√33)/2, (-1-√33)/2}

theorem arany2024_advanced_i_i_iii {x : ℝ} : x^4 - 11*x^2 + 25 = -6*x + 9 ↔ x ∈ SolutionSet := by
  unfold SolutionSet
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff]
  have : (√33)^2 = 33 := by exact Real.sq_sqrt (by norm_num)

  constructor
  · intro h
    
    have : (x^2 - 5)^2 = (x-3)^2 := by linarith
    rw [sq_eq_sq_iff_eq_or_eq_neg] at this

    rcases this with h1 | h1
    · have : (x+1)*(x-2) = 0 := by linarith
      simp at this

      rcases this with h2 | h2
      · left
        linarith
      · right
        left
        linarith
    · have : (x-(-1+√33)/2)*(x-(-1-√33)/2) = 0 := by linarith
      simp at this
      
      rcases this with h2 | h2
      · right
        right
        left
        linarith
      · right
        right
        right
        linarith
  · intro h

    rcases h with rfl | rfl | rfl |rfl
    all_goals nlinarith
