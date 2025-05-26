import Mathlib.Tactic

/-
Arany Dániel 2022/2023 Haladók II. kategória III. forduló 1. feladat

Határozzuk meg az összes olyan n pozitív egész számot, amelynek létezik három olyan a > b > c
pozitív osztója, hogy a^2 - b^2, b^2 - c^2, a^2 - c^2 is osztója n-nek
-/
theorem arany2023_advanced_ii_iii_i (n : ℤ) (hnpos : n > 0) 
  : (∃ (a b c : ℤ), a > 0 ∧ b > 0 ∧ c > 0 ∧ (a^2 - b^2 ∣ n) ∧ (b^2 - c^2 ∣ n) ∧ (a^2 - c^2 ∣ n) ∧ (a ∣ n) ∧ (b ∣ n) ∧ (c ∣ n)) ↔ 60 ∣ n := by
  constructor
  · intro h
    obtain ⟨a, b, c, hapos, hbpos, hcpos, h1, h2, h3, hadiv, hbdiv, hcdiv⟩ := h
    
    -- ugly but it works - maybe use pigeonhole principle somehow?
    -- the main argument is that if we have 3 numbers two will have matching parities
    have hndiv4 : 4 ∣ n := by
      by_cases ha: a%2 = 0
      · by_cases hb: b%2 = 0
        · have : 2 ∣ a := by exact Int.dvd_of_emod_eq_zero ha
          obtain ⟨x, hx⟩ := this

          have : 2 ∣ b := by exact Int.dvd_of_emod_eq_zero hb
          obtain ⟨y, hy⟩ := this

          rw [hx, hy] at h1
          have : (2 * x) ^ 2 - (2 * y) ^ 2 = 4*(x^2 - y^2) := by ring
          rw [this] at h1

          exact dvd_of_mul_right_dvd h1
        · by_cases hc: c%2 = 0
          · have : 2 ∣ a := by exact Int.dvd_of_emod_eq_zero ha
            obtain ⟨x, hx⟩ := this

            have : 2 ∣ c := by exact Int.dvd_of_emod_eq_zero hc
            obtain ⟨y, hy⟩ := this

            rw [hx, hy] at h3
            have : (2 * x) ^ 2 - (2 * y) ^ 2 = 4*(x^2 - y^2) := by ring
            rw [this] at h3

            exact dvd_of_mul_right_dvd h3
          · have : b%2 = 1 := by exact Int.emod_two_ne_zero.mp hb
            have : 2 ∣ (b-1) := by exact Int.dvd_of_emod_eq_zero (by exact Int.emod_eq_emod_iff_emod_sub_eq_zero.mp this)
            obtain ⟨x, hx⟩ := this
            have hx : b = 2*x+1 := by linarith

            have : c%2 = 1 := by exact Int.emod_two_ne_zero.mp hc
            have : 2 ∣ (c-1) := by exact Int.dvd_of_emod_eq_zero (by exact Int.emod_eq_emod_iff_emod_sub_eq_zero.mp this)
            obtain ⟨y, hy⟩ := this
            have hy : c = 2*y+1 := by linarith

            rw [hx, hy] at h2
            have : (2 * x + 1) ^ 2 - (2 * y + 1) ^ 2 = 4*(x^2 + x - y^2 - y) := by ring
            rw [this] at h2

            exact dvd_of_mul_right_dvd h2
      · by_cases hb: b%2 = 0
        · by_cases hc: c%2 = 0
          · have : 2 ∣ b := by exact Int.dvd_of_emod_eq_zero hb
            obtain ⟨x, hx⟩ := this

            have : 2 ∣ c := by exact Int.dvd_of_emod_eq_zero hc
            obtain ⟨y, hy⟩ := this

            rw [hx, hy] at h2
            have : (2 * x) ^ 2 - (2 * y) ^ 2 = 4*(x^2 - y^2) := by ring
            rw [this] at h2

            exact dvd_of_mul_right_dvd h2
          · have : a%2 = 1 := by exact Int.emod_two_ne_zero.mp ha
            have : 2 ∣ (a-1) := by exact Int.dvd_of_emod_eq_zero (by exact Int.emod_eq_emod_iff_emod_sub_eq_zero.mp this)
            obtain ⟨x, hx⟩ := this
            have hx : a = 2*x+1 := by linarith

            have : c%2 = 1 := by exact Int.emod_two_ne_zero.mp hc
            have : 2 ∣ (c-1) := by exact Int.dvd_of_emod_eq_zero (by exact Int.emod_eq_emod_iff_emod_sub_eq_zero.mp this)
            obtain ⟨y, hy⟩ := this
            have hy : c = 2*y+1 := by linarith

            rw [hx, hy] at h3
            have : (2 * x + 1) ^ 2 - (2 * y + 1) ^ 2 = 4*(x^2 + x - y^2 - y) := by ring
            rw [this] at h3

            exact dvd_of_mul_right_dvd h3
        · have : a%2 = 1 := by exact Int.emod_two_ne_zero.mp ha
          have : 2 ∣ (a-1) := by exact Int.dvd_of_emod_eq_zero (by exact Int.emod_eq_emod_iff_emod_sub_eq_zero.mp this)
          obtain ⟨x, hx⟩ := this
          have hx : a = 2*x+1 := by linarith

          have : b%2 = 1 := by exact Int.emod_two_ne_zero.mp hb
          have : 2 ∣ (b-1) := by exact Int.dvd_of_emod_eq_zero (by exact Int.emod_eq_emod_iff_emod_sub_eq_zero.mp this)
          obtain ⟨y, hy⟩ := this
          have hy : b = 2*y+1 := by linarith

          rw [hx, hy] at h1
          have : (2 * x + 1) ^ 2 - (2 * y + 1) ^ 2 = 4*(x^2 + x - y^2 - y) := by ring
          rw [this] at h1

          exact dvd_of_mul_right_dvd h1

    

    sorry
  · intro h
    use 4, 2, 1

    obtain ⟨k, hk⟩ := h
    rw [hk]
    omega
