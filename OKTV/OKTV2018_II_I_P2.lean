import Mathlib.Tactic
/-
OKTV 2018/2019, II. kategória, I. forduló, 2. feladat:

Melyik a nagyobb szám: (2018!)^(1/2018) vagy (2019!)^(1/2019)
----
bizonyítsuk be, hogy a (2019!)^(1/2019) nagyobb
-/
set_option exponentiation.threshold 2020

theorem oktv2018_ii_i_ii : (Nat.factorial 2019 : ℝ)^(1/2019 : ℝ) > (Nat.factorial 2018 : ℝ)^(1/2018 : ℝ) := by
  have : (Nat.factorial 2019 : ℝ)^(1/2019 : ℝ) > (Nat.factorial 2018 : ℝ)^(1/2018 : ℝ)
    ↔ ((Nat.factorial 2019 : ℝ)^(1/2019 : ℝ))^(2018*2019 : ℝ) > ((Nat.factorial 2018 : ℝ)^(1/2018 : ℝ))^(2018*2019 : ℝ) := by
    norm_cast
    refine Iff.symm (pow_lt_pow_iff_left₀ ?_ ?_ ?_)
    refine Real.rpow_nonneg ?_ (1 / 2018)
    norm_num
    refine Real.rpow_nonneg ?_ (1 / 2019)
    norm_num
    norm_num

  rw [this]
  simp [← Real.rpow_mul]
  norm_num

  have h2018_fac_pos : (Nat.factorial 2018 : ℝ) > 0 := by
    norm_num
    exact Nat.factorial_pos 2018

  have : ((Nat.factorial 2018 : ℝ)^(2018 : ℝ)) > 0 := by
    refine Real.rpow_pos_of_pos ?_ 2018
    exact h2018_fac_pos

  rw [← div_lt_div_iff_of_pos_right this]
  rw [← Real.rpow_sub h2018_fac_pos]
  norm_num

  have : Nat.factorial 2019 = 2019 * Nat.factorial 2018 := by rw [Nat.factorial_succ]
  rw [this]

  push_cast
  rw [Real.mul_rpow (by norm_num) (by norm_num)]
  field_simp
  norm_cast0

  have : Nat.factorial 2018 ≤ 2018^2018 := by exact Nat.factorial_le_pow 2018

  linarith
