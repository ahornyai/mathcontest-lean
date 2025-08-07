import Mathlib.Tactic

/-
Arany Dániel 2014/2015 Haladók II. kategória, I. forduló III. feladat

Jelöljön x, y, z olyan pozitív egész számokat, amelyekre teljesül, hogy 2*x*y^2 = 3*z^3.
Mennyi az xyz szorzat minimuma?
------------------
Bizonyítsuk, hogy a szorzat minimuma 12
-/
theorem arany2014_advanced_ii_i_iii (x y z : ℕ) (hxpos : x > 0) (hypos : y > 0) (hzpos : z > 0) (h : 2*x*y^2 = 3*z^3) : x*y*z ≥ 12 := by
  have : Even (3*z^3) := by
    rw [← h, mul_assoc]
    exact even_two_mul (x * y ^ 2)

  have hz_even : 2 ∣ z := by
    have : Even (z^3) := by
      have : 2 ∣ 3*z^3 := by exact even_iff_two_dvd.mp this
      rw [Nat.Coprime.dvd_mul_left] at this

      exact (even_iff_exists_two_nsmul (z ^ 3)).mpr this
      decide

    rw [Nat.even_pow' (by decide)] at this

    exact even_iff_two_dvd.mp this

  have hxy_div_3 : 3 ∣ x ∨ 3 ∣ y := by
    have : 3 ∣ 2*x*y^2 := by exact Dvd.intro (z ^ 3) (id (Eq.symm h))
    have : 3 ∣ x*y^2 := by
      rw [mul_assoc, Nat.Coprime.dvd_mul_left] at this
      exact this
      decide

    have : 3 ∣ x ∨ 3 ∣ y^2 := by refine (Nat.Prime.dvd_mul (by exact Nat.prime_three)).mp this

    rcases this with h1 | h1
    · exact Or.inl h1
    · apply Nat.Prime.dvd_of_dvd_pow at h1

      exact Or.inr h1
      exact Nat.prime_three

  have : 6 ∣ x*y*z := by
    have : 6 = 3*2 := by decide
    rw [this]

    rcases hxy_div_3 with h1 | h1
    · refine Nat.mul_dvd_mul ?_ hz_even
      exact Dvd.dvd.mul_right h1 y
    · refine Nat.mul_dvd_mul ?_ hz_even
      exact Dvd.dvd.mul_left h1 x
  obtain ⟨k, hk⟩ := this
  rw [hk]

  by_contra!
  have : k > 0 := by
    have : 6*k > 0 := by
      rw [← hk]

      refine Nat.mul_pos ?_ hzpos
      refine Nat.mul_pos hxpos hypos

    exact Nat.pos_of_mul_pos_left this

  have hk_eq : k = 1 := by omega
  rw [hk_eq] at hk
  norm_num at hk

  have : z ≤ 6 := by
    by_contra!
    have : x*y*z > 6 := by
      have h2 : y*z > 0 := by exact Nat.mul_pos hypos hzpos
      nlinarith

    omega

  interval_cases z <;> nlinarith
