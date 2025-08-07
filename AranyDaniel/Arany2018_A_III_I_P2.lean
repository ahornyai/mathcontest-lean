import Mathlib.Tactic

/-
Arany Dániel 2018/2019 Haladók III. kategória I. forduló II. feladat

Mely x, y pozitív számokra teljesül a következő egyenlet?
x^2 + y^2 + x + y = 2*√(x^3 + y^3 + x^2*y^2 + x*y)
---------------------
Bizonyítsuk, hogy x=y valamint y=1-x esetén teljesül
-/
lemma amgm_eq {x y : ℝ} (hxpos : x > 0) (hypos : y > 0) : √(x*y) = (x+y)/2 ↔ x=y :=by
  constructor
  · intro h
    rw [Real.sqrt_eq_iff_eq_sq] at h

    all_goals nlinarith
  · intro h
    rw [h]
    field_simp

theorem arany2018_advanced_iii_i_ii (x y : ℝ) (hxpos : x > 0) (hypos : y > 0)
  : x^2 + y^2 + x + y = 2*√(x^3 + y^3 + x^2*y^2 + x*y) ↔ y=x ∨ y=1-x := by
  constructor
  · intro h

    have : √((x ^ 2 + y) * (y ^ 2 + x)) = ((x ^ 2 + y) + (y ^ 2 + x)) / 2 := by
      have : x^3 + y^3 + x^2*y^2 + x*y = (x ^ 2 + y) * (y ^ 2 + x) := by ring
      rw [this] at h
      linarith
    rw [amgm_eq (by nlinarith) (by nlinarith)] at this

    have : (x-y)*(x+y-1) = 0 := by linarith
    simp at this

    rcases this with h1 | h1
    · have : y=x := by linarith
      exact Or.inl this
    · have : y = 1-x := by linarith
      exact Or.inr this
  · intro h
    rcases h with rfl | rfl
    · have : y ^ 2 + y ^ 2 + y + y = 2*(y^2 + y) := by linarith
      rw [this, mul_right_inj' (by norm_num)]

      have : y ^ 3 + y ^ 3 + y ^ 2 * y ^ 2 + y * y = (y^2 + y)^2 := by ring
      rw [this, Real.sqrt_sq (by nlinarith)]
    · have : x ^ 2 + (1 - x) ^ 2 + x + (1 - x) = 2*(x^2 - x + 1) := by ring
      rw [this, mul_right_inj' (by norm_num)]

      have : (x ^ 3 + (1 - x) ^ 3 + x ^ 2 * (1 - x) ^ 2 + x * (1 - x)) = (x^2 - x + 1)^2 := by ring
      rw [this, Real.sqrt_sq (by nlinarith)]
