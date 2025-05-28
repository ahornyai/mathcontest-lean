import Mathlib.Tactic

/-
Arany Dániel 2013/2014 Haladók II. kategória, II. forduló III. feladat

Oldjuk meg az egész számok halmazán a 2*x^2*y^2 + y^2 = 6*x^2 + 12 egyenletet
----------------------
Bizonyítsuk, hogy a megoldáshalmaz: (x, y) ∈ {(2, 2), (2, -2), (-2, 2), (-2, -2)}
-/
def SolutionSet : Set (ℤ × ℤ) :={(2, 2), (2, -2), (-2, 2), (-2, -2)}

example {a b : ℤ} (hb2 : b ≠ 0) : a*b/b = a := by
  exact Int.mul_ediv_cancel a hb2

theorem arany2014_advanced_ii_ii_iii (x y : ℤ) : 2*x^2*y^2 + y^2 = 6*x^2 + 12 ↔ ⟨x, y⟩ ∈ SolutionSet := by
  unfold SolutionSet
  simp
  
  constructor
  · intro h
    have : 2 * (3 - y ^ 2) * x ^ 2 = y ^ 2 - 12 := by linarith
    
    have hxsq_eq : x^2 = (y^2 - 12) / (2*(3 - y^2)) := by
      refine Int.eq_ediv_of_mul_eq_right ?_ ?_
      nlinarith
      exact this
    
    have hdiv : (2*(3 - y^2)) ∣ (y^2 - 12) := by exact Dvd.intro (x ^ 2) this
    obtain ⟨k, hk⟩ := hdiv
    
    have h1 : 0 ≤ (y^2 - 12) / (2*(3 - y^2)) := by
      rw [← hxsq_eq]
      exact sq_nonneg x
    
    by_cases h2: (y^2 - 12) ≥ 0
    · have : (2*(3 - y^2)) > 0 := by
        by_contra!
        have h1_contra : (y^2 - 12) / (2*(3 - y^2)) ≤ 0 := by exact Int.ediv_nonpos_of_nonneg_of_nonpos h2 this
        
        have : (y ^ 2 - 12) = 0 := by
          have : (y ^ 2 - 12) / (2 * (3 - y ^ 2)) = 0 := by omega
        
          rw [hk] at this
          rw [Int.mul_ediv_cancel_left k ?_] at this
          rw [this, mul_zero] at hk
          
          exact hk
          linarith
        
        have : IsSquare ((12 : ℤ)) := by
          use y
          linarith
        have : ¬ IsSquare ((12 : ℤ)) := by decide

        contradiction
      
      nlinarith
    · push_neg at h2
      have : (2*(3 - y^2)) < 0 := by
        by_contra!
        have h1_contra : (y^2 - 12) / (2*(3 - y^2)) < 0 := by nlinarith
        linarith
      
      have : y^2 < 12 := by linarith
      have : 3 < y^2 := by linarith

      have : y^2 = 4 ∨ y^2 = 9 := by
        by_contra!
        have h3 : IsSquare (y^2) := by exact IsSquare.sq y
        have h3_contra : ¬ IsSquare (y^2) := by interval_cases y^2 <;> trivial
        contradiction
      
      rcases this with h3 | h3
      · have : (y+2)*(y-2) = 0 := by linarith
        simp at this

        have : (x+2)*(x-2) = 0 := by nlinarith
        simp at this

        rcases this with h5 | h5 <;> omega
      · have : 4*x^2 = 1 := by nlinarith

        have : 4 ∣ (1 : ℤ) := by exact Dvd.intro (x ^ 2) this
        have : ¬ 4 ∣ (1 : ℤ) := by decide

        contradiction
  · intro h
    rcases h with h | h | h | h
    all_goals
      obtain ⟨rfl, rfl⟩ := h
      norm_num
