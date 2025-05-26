import Mathlib.Tactic

/-
Arany Dániel 2022/2023 Haladók III. kategória II. forduló 1. feladat

Bizonyítsuk be, hogy egyetlen olyan n pozitív egész szám van, amelyre 3*n + 1 és 7*n + 4 is
négyzetszám, valamint n + 7 prímszám.
-/
theorem arany2023_advanced_iii_ii_i (n : ℕ) (hnpos : n > 0) : (IsSquare (7*n+4) ∧ IsSquare (3*n+1) ∧ Nat.Prime (n+7)) ↔ n=96 := by
  constructor
  · intro h
    obtain ⟨h1, h2, h3⟩ := h

    obtain ⟨a, ha⟩ := h1
    obtain ⟨b, hb⟩ := h2

    have h1 : n+7 = (2*a+3*b)*(2*a-3*b) := by
      have : (2*a+3*b)*(2*a-3*b) = 4*a^2 - 9*b^2 := by
        rw [Nat.mul_sub_left_distrib]
        ring_nf
        exact Nat.add_sub_add_left (a * b * 6) (a ^ 2 * 4) (b ^ 2 * 9)
      rw [this]

      refine Eq.symm (Nat.sub_eq_of_eq_add ?_)
      linarith
    
    have h2 : 2*a+3*b = 1 ∨ 2*a+3*b = n+7 := by
      refine (Nat.dvd_prime h3).mp ?_
      exact Dvd.intro (2 * a - 3 * b) (id (Eq.symm h1))
    
    have h3 : 2*a-3*b = 1 ∨ 2*a-3*b = n+7 := by
      refine (Nat.dvd_prime h3).mp ?_
      exact Dvd.intro_left (2 * a + 3 * b) (id (Eq.symm h1))

    rcases h2 with h2 | h2
    · omega
    · rcases h3 with h3 | h3
      · have : n+6 = 6*b := by nlinarith
        
        nlinarith
      · nlinarith
  · intro h
    rw [h]
    norm_num
    exact ⟨(by use 26), (by use 17)⟩
