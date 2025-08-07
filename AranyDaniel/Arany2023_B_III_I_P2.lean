import Mathlib.Tactic

/-
Arany Dániel 2023/2024 Kezdők III. kategória I. forduló II. feladat

Legyenek x, y, z pozitív valós számok úgy, hogy x + y + z = 2024. Bizonyítsuk be, hogy
√(x*y+x*z) + √(x*y+y*z) + √(x*z+y*z) ≤ 3036
-/
lemma amgm {a b : ℝ} (hapos : a > 0) (hbpos : b > 0) : √(a*b) ≤ (a+b)/2 := by
  rw [Real.sqrt_le_left ?_]
  rw [div_pow, add_pow_two, le_div_iff₀ (by norm_num), ← sub_nonneg]

  have : a ^ 2 + 2 * a * b + b ^ 2 - a * b * 2 ^ 2 = (a-b)^2 := by ring
  rw [this]

  exact sq_nonneg (a - b)
  linarith

theorem arany2023_beginner_iii_i_ii {x y z : ℝ} (hxpos : x > 0) (hypos : y > 0) (hzpos : z > 0) (h : x+y+z=2024)
  : √(x*y+x*z) + √(x*y+y*z) + √(x*z+y*z) ≤ 3036 := by

  have h1 : √(x*y+x*z) ≤ (x+(y+z))/2 := by
    have : x*y+x*z = x*(y+z) := by ring
    rw [this]
    apply amgm hxpos (by linarith)

  have h2 : √(x*y+y*z) ≤ (y+(x+z))/2 := by
    have : x*y+y*z = y*(x+z) := by ring
    rw [this]
    apply amgm hypos (by linarith)

  have h3 : √(x*z+y*z) ≤ (z+(x+y))/2 := by
    have : x*z+y*z = z*(x+y) := by ring
    rw [this]
    apply amgm hzpos (by linarith)

  linarith
