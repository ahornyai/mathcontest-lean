import Mathlib.Tactic

/-
Arany Dániel 2012/2013 Kezdők II. kategória III. forduló III. feladat

Az x, y, z egész számokra teljesül, hogy x + y + z = 2.
Tudjuk, hogy az 1/(x*y + z - 1) + 1/(y*z + x - 1) + 1/(z*x + y - 1)
összeg egy prímszám reciprokával egyenlő.
Melyik ez a prímszám?
-----------------------------------
Bizonyítsuk, hogy ez a prímszám a 3
-/
theorem arany2012_beginner_ii_iii_iii (x y z p : ℤ) (hp : Prime p) (hx_neq_1 : x-1 ≠ 0) (hy_neq_1 : y-1 ≠ 0) (hz_neq_1 : z-1 ≠ 0)
  (h1 : x + y + z = 2) (h2 : (1/p : ℚ) = 1/(x*y + z - 1) + 1/(y*z + x - 1) + 1/(z*x + y - 1)) : p=3 := by
  have : ((x*y + z - 1) : ℚ) = (x-1)*(y-1) := by norm_cast; linarith
  rw [this] at h2

  have : ((y*z + x - 1) : ℚ) = (y-1)*(z-1) := by norm_cast; linarith
  rw [this] at h2

  have : ((z*x + y - 1) : ℚ) = (z-1)*(x-1) := by norm_cast; linarith
  rw [this] at h2

  have hxy_neq_0 : ((x - 1) * (y - 1) : ℚ) ≠ 0 := by
    refine (mul_ne_zero_iff_right ?_).mpr ?_
    norm_cast
    norm_cast

  have hyz_neq_0 : ((y - 1) * (z - 1) : ℚ) ≠ 0 := by
    refine (mul_ne_zero_iff_right ?_).mpr ?_
    norm_cast
    norm_cast

  have hxyz_neq_0 : ((x-1)*(y-1)*(z-1) : ℚ) ≠ 0 := by
    refine (mul_ne_zero_iff_right ?_).mpr ?_
    norm_cast
    exact hxy_neq_0

  have h3 : (1/p : ℚ)= (x+y+z-3)/((x-1)*(y-1)*(z-1)) := by
    repeat rw [div_add_div] at h2

    have : (((1 * ((y - 1) * (z - 1)) + (x - 1) * (y - 1) * 1) * ((z - 1) * (x - 1)) + (x - 1) * (y - 1) * ((y - 1) * (z - 1)) * 1)) = ((x+y+z-3)*((x-1)*(y-1)*(z-1)) : ℚ) := by ring_nf
    rw [this] at h2

    have : ((x - 1) * (y - 1) * ((y - 1) * (z - 1)) * ((z - 1) * (x - 1)) : ℚ) = ((x-1)*(y-1)*(z-1)) * ((x-1)*(y-1)*(z-1)) := by ring_nf
    rw [this] at h2

    have : (((x+y+z-3)*((x-1)*(y-1)*(z-1))) / (((x-1)*(y-1)*(z-1)) * ((x-1)*(y-1)*(z-1))) : ℚ) = (x+y+z-3) / ((x-1)*(y-1)*(z-1)) := by
      apply Eq.symm (div_eq_of_eq_mul hxyz_neq_0 ?_)
      field_simp
      ring_nf
    rw [this] at h2

    exact h2

    refine (mul_ne_zero_iff_right ?_).mpr ?_
    exact hyz_neq_0
    exact hxy_neq_0

    refine (mul_ne_zero_iff_right ?_).mpr ?_
    norm_cast
    norm_cast

    exact hxy_neq_0
    exact hyz_neq_0
  have : (x+y+z : ℚ) = 2 := by norm_cast
  rw [this] at h3

  have : (p : ℚ) ≠ 0 := by
    norm_cast
    by_contra!
    rw [this] at hp
    have : ¬ Prime (0 : ℤ) := by norm_num
    contradiction

  field_simp at h3
  norm_num at h3
  norm_cast at h3

  have : p ∣ (x - 1) * ((y - 1) * (z - 1)) := by
    rw [← mul_assoc, h3]
    refine Int.dvd_neg.mpr ?_
    rfl

  have : p ∣ (x-1) ∨ p ∣ ((y - 1) * (z - 1)) := by
    exact Prime.dvd_or_dvd hp this

  have : p ∣ (x-1) ∨ p ∣ (y - 1) ∨ p ∣ (z - 1) := by
    rcases this with h4 | h4
    · left
      exact h4
    · right
      exact Prime.dvd_or_dvd hp h4

  rcases this with h4 | h4 | h4
  · sorry
  · sorry
  · sorry
example {a b c d : ℝ} (ha : a ≠ 0) (hc : c ≠ 0) (hd : d ≠ 0) (hb : b ≠ 0) : a/c = b/d ↔ c/a = d/b := by
  exact div_eq_div_iff_comm a c b
