import Mathlib.Tactic

/-
Arany Dániel 2022/2023 Kezdők I. kategória I. forduló III. feladat

Melyik az a legnagyobb n egész szám, amelyre n^2 + 2022 osztható (n + 10)-zel? 
-----
bizonyítsuk, hogy a legnagyobb n szám: n=2112
-/
theorem arany2023_beginner_i_i_iii : IsGreatest {n : ℤ | (n+10)∣(n^2 + 2022)} 2112 := by
  unfold IsGreatest upperBounds

  constructor
  · use (2112^2 + 2022)/(2112+10)
    norm_num
  · simp only [Set.mem_setOf_eq]
    intro n
    contrapose!
    intro h1 h
    
    have h1div : n+10 ∣ n^2 - 100 := by
      have : (100 : ℤ) = 10^2 := by norm_num
      rw [this, sq_sub_sq]
      exact Int.dvd_mul_right (n + 10) (n - 10)
    
    have h2div : n+10 ∣ 2122 := by
      have : 2122 = (n^2 + 2022) - (n^2 - 100) := by ring_nf
      rw [this]
      exact Int.dvd_sub h h1div
    
    obtain ⟨k, hk⟩ := h2div

    have : (n+10) ≤ 2122 := by
      by_contra!
      
      by_cases h2: k > 0
      all_goals nlinarith
    
    linarith
