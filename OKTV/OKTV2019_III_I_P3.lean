import Mathlib.Tactic
/-
OKTV 2009/2010, III. kategória, I. forduló, 3. feladat:

Oldjuk meg a
(2*x+2)*(5-2*x)*(4*x^2 + 8*x + 11) = 10*(2*x+3)^2
egyenletet a valós számok körében.
--------------------------------
bizonyítsuk be, hogy az összes megoldás: x=(1+√17)/4, x=(1-√17)/4
-/
theorem oktv2009_iii_i_iii (x : ℝ) : (2*x+2)*(5-2*x)*(4*x^2 + 8*x + 11) = 10*(2*x+3)^2 ↔ x=(1+√17)/4 ∨ x=(1-√17)/4 := by
  constructor
  · intro h
    have : (2*x+2) * (5-2*x) = -4*x^2 + 6*x + 10 := by ring_nf
    rw [this] at h

    have h2xp3_neq_0 : 2*x+3 ≠ 0 := by
      by_contra!
      nlinarith

    have : (2*x+3)^2 ≠ 0 := by
      by_contra!
      rw [pow_eq_zero_iff] at this
      nlinarith
      norm_num

    symm at h
    rw [← eq_div_iff this] at h
    rw [pow_two (2*x+3)] at h
    rw [mul_div_mul_comm _ _ (2*x+3) (2*x+3)] at h

    let A := (-4*x^2 + 6*x + 10)/(2*x+3)
    let B := (4*x^2 + 8*x + 11)/(2*x+3)

    have hab_prod : A*B = 10 := by linarith
    have hab_sum : A+B = 7 := by
      unfold A B
      rw [div_add_div_same]

      have : (-4 * x ^ 2 + 6 * x + 10 + (4 * x ^ 2 + 8 * x + 11)) = 7*(2*x+3) := by ring_nf
      rw [this]
      exact mul_div_cancel_right₀ 7 h2xp3_neq_0

    have hb_eq : B=(7-A) := by linarith
    have : A^2 - 7*A + 10 = 0 := by nlinarith
    have : (A-5)*(A-2) = 0 := by linarith
    simp at this

    rcases this with h1 | h1
    · have ha_eq : A=5 := by linarith
      unfold A at ha_eq

      rw [div_eq_iff h2xp3_neq_0] at ha_eq

      have : 4*x^2 + 4*x + 5 = 0 := by linarith
      have : 4*x^2 + 4*x + 5 ≠ 0 := by nlinarith

      contradiction
    · have ha_eq : A=2 := by linarith
      unfold A at ha_eq

      rw [div_eq_iff h2xp3_neq_0] at ha_eq

      have : 2*x^2 - x - 2 = 0 := by linarith
      have : (x-(1+√17)/4)*(x-(1-√17)/4) = 0 := by
        have : √17*√17 = 17 := by exact Real.mul_self_sqrt (by norm_num)
        linarith
      simp at this

      rcases this with h1 | h1
      · have : x = (1+√17)/4 := by linarith
        left
        exact this
      · have : x = (1-√17)/4 := by linarith
        right
        exact this
  · intro h
    have : √17*√17 = 17 := by exact Real.mul_self_sqrt (by norm_num)

    rcases h with rfl | rfl
    all_goals nlinarith
