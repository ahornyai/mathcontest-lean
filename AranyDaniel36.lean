import Mathlib.Tactic

/-
Arany Dániel 2019/2020 Haladók III. kategória II. forduló 2. feladat

Az x, y, z pozitív valós számok szorzata 1. Bizonyítsuk be, hogy x/(y+z+3) + y/(x+z+3) + z/(x+y+3) ≥ 3/5
-/
lemma reciprocal_sum_geq_2 {x y : ℝ} (hxpos : x > 0) (hypos : y > 0) : x/y + y/x ≥ 2 := by
  field_simp

  rw [le_div_iff₀', ← sub_nonneg]

  have : x * x + y * y - y * x * 2 = (x - y)^2 := by ring
  rw [this]

  exact sq_nonneg (x - y)
  exact Left.mul_pos hypos hxpos

theorem arany2020_advanced_iii_ii_ii (x y z : ℝ) (h : x*y*z = 1) (hxpos : x > 0) (hypos : y > 0) (hzpos : z > 0)
  : x/(y+z+3) + y/(x+z+3) + z/(x+y+3) ≥ 3/5 := by
  have h₁ : x+y+z ≥ 3 := by
    have : x^(1/3 : ℝ) * y^(1/3 : ℝ) * z^(1/3 : ℝ) ≤ 1/3 * x + 1/3 * y + 1/3 * z := by
      apply Real.geom_mean_le_arith_mean3_weighted
      all_goals linarith
    
    rw [← Real.mul_rpow, ← Real.mul_rpow, h, Real.one_rpow] at this
    
    all_goals nlinarith
    
  have h₂ : x/(y+z+3) + y/(x+z+3) + z/(x+y+3) ≥ x/(y+z+x+y+z) + y/(x+z+x+y+z) + z/(x+y+x+y+z) := by
    refine add_le_add_three ?_ ?_ ?_
    
    all_goals
    exact div_le_div_of_nonneg_left (by linarith) (by linarith) (by linarith)

  have h₃ : x/(y+z+x+y+z) + y/(x+z+x+y+z) + z/(x+y+x+y+z) ≥ 3/5 := by
    let a := x + 2*y + 2*z
    let b := 2*x + y + 2*z
    let c := 2*x + 2*y + z

    have hapos : a > 0 := by linarith
    have hbpos : b > 0 := by linarith
    have hcpos : c > 0 := by linarith

    have hx : x = -3/5*a + 2/5*b + 2/5*c := by linarith
    have hy : y = 2/5*a + -3/5*b + 2/5*c := by linarith
    have hz : z = 2/5*a + 2/5*b + -3/5*c := by linarith

    have : x/(y+z+x+y+z) + y/(x+z+x+y+z) + z/(x+y+x+y+z) = -9/5 + 2/5*((b/c + c/b) + (a/b + b/a) + (a/c + c/a)) := by
      have : x/(y+z+x+y+z) + y/(x+z+x+y+z) + z/(x+y+x+y+z) = (-3/5*a + 2/5*b + 2/5*c)/a + (2/5*a + -3/5*b + 2/5*c)/b + (2/5*a + 2/5*b + -3/5*c)/c := by
        rw [← hx, ← hy, ← hz]
        field_simp
        ring
      
      rw [this]
      field_simp
      ring
    rw [this]

    have : b/c + c/b ≥ 2 := by exact reciprocal_sum_geq_2 hbpos hcpos
    have : a/b + b/a ≥ 2 := by exact reciprocal_sum_geq_2 hapos hbpos
    have : a/c + c/a ≥ 2 := by exact reciprocal_sum_geq_2 hapos hcpos

    linarith

  linarith
