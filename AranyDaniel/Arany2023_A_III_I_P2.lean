import Mathlib.Tactic

/-
Arany Dániel 2023/2024 Haladók III. kategória I. forduló II. feladat

Legyen n pozitív egész szám, d pedig az n^2 + 1 és az (n + 1)^2 + 1 számok legnagyobb közös osztója.
Határozzuk meg d lehetséges értékeit.
-----
bizonyítsuk, hogy a d lehetséges értékei: {1, 5}
-/
theorem eq_of_mul_eq_five {x y : ℕ} (h : x * y = 5) :
    x = 1 ∧ y = 5 ∨ x = 5 ∧ y = 1 := by
  have h₁ : (x, y) ∈ Nat.divisorsAntidiagonal 5 := by simpa using h
  have h₂ : Nat.divisorsAntidiagonal 5 = {(1, 5), (5, 1)} := by rfl
  simpa [h₂] using h₁

theorem arany2023_advanced_iii_i_ii {n d : ℕ} (hnpos : n > 0) (h: d = Nat.gcd (n^2 + 1) ((n+1)^2 + 1))
  : d = 1 ∨ d = 5 := by
  have hd_div_n2p1 : d ∣ (n^2 + 1) := by
    rw [h]
    exact Nat.gcd_dvd_left (n ^ 2 + 1) ((n + 1) ^ 2 + 1)

  have hd_div_np12p1 : d ∣ (n+1)^2 + 1 := by
    rw [h]
    exact Nat.gcd_dvd_right (n ^ 2 + 1) ((n + 1) ^ 2 + 1)

  have h1 : d ∣ 4*n^2 + 4 := by
    have : 4*n^2 + 4 = 4*(n^2 + 1) := by ring_nf
    rw [this]
    exact Nat.dvd_mul_left_of_dvd hd_div_n2p1 4

  have h2 : d ∣ 4*n^2-1 := by
    have : 4*n^2-1 = (2*n)^2 - 1^2 := by ring_nf
    rw [this, Nat.sq_sub_sq]

    have : d ∣ 2*n+1 := by
      have : ((n + 1) ^ 2 + 1) - (n^2 + 1) = 2*n + 1 := by
        rw [add_pow_two]
        norm_num
        rw [Nat.sub_eq_iff_eq_add]
        linarith
        linarith

      rw [← this]
      exact Nat.dvd_sub hd_div_np12p1 hd_div_n2p1

    exact Nat.dvd_mul_right_of_dvd this (2 * n - 1)

  have : d ∣ 5 := by
    have : (4*n^2 + 4) - (4*n^2-1) = 5 := by
      rw [← Nat.eq_sub_of_add_eq']
      rw [← Nat.eq_add_of_sub_eq]
      nlinarith
      rfl

    rw [← this]
    exact Nat.dvd_sub h1 h2

  obtain ⟨k, hk⟩ := this
  symm at hk
  apply eq_of_mul_eq_five at hk

  omega
