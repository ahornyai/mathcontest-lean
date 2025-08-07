import Mathlib.Tactic

/-
Arany Dániel 2016/2017 Haladók II. kategória II. forduló I. feladat

Igazoljuk, hogy az x!*(x + 4)! = y^2 egyenletnek nincs megoldása, ha x és y pozitív egész
számok!
-/
lemma sq_mul_x_is_sq {a x b : ℕ} (ha : a ≠ 0) (h : a*x = b) (ha_sq : IsSquare a) (hb_sq : IsSquare b) : IsSquare x := by
  rcases ha_sq with ⟨c, rfl⟩
  rcases hb_sq with ⟨d, rfl⟩

  -- a = c^2 és b = d^2
  have h1 : c^2 * x = d^2 := by linarith

  -- Most megmutatjuk, hogy d osztható c-vel
  have h_div_sq : c^2 ∣ d^2 := by exact Dvd.intro x h1

  have h_div : c ∣ d := by
    rw [Nat.pow_dvd_pow_iff] at h_div_sq

    exact h_div_sq
    norm_num

  -- Legyen d = c * k valamilyen k-ra
  rcases h_div with ⟨k, hk⟩
  subst hk

  -- Most átrendezzük a jobb oldalt
  have h2 : c * c * x = c * c * (k * k) := by
    rw [h]
    ring

  have h3 : x = k * k := by
    have hc2 : c * c > 0 := by omega

    apply Nat.eq_of_mul_eq_mul_left hc2
    exact h2

  use k

theorem arany2016_advanced_ii_ii_i  : ¬ ∃ x y : ℕ, (x > 0) ∧ (y > 0) ∧ ((x).factorial * (x+4).factorial = y^2) := by
  intro h
  obtain ⟨x, y, hxpos, hypos, h⟩ := h

  have : (x+4).factorial = (x+4)*(x+3)*(x+2)*(x+1)*(x).factorial := by
    nth_rewrite 1 [Nat.factorial]
    nth_rewrite 1 [Nat.factorial]
    nth_rewrite 1 [Nat.factorial]
    nth_rewrite 1 [Nat.factorial]

    linarith
  rw [this] at h

  have h1 : (x.factorial)^2 * ((x+4)*(x+3)*(x+2)*(x+1)) = y^2 := by linarith

  have hx_sq : IsSquare ((x.factorial)^2) := by exact IsSquare.sq x.factorial
  have hy_sq : IsSquare (y^2) := by exact IsSquare.sq y

  have : IsSquare ((x+4)*(x+3)*(x+2)*(x+1)) := by
    have : (x.factorial)^2 ≠ 0 := by
      refine pow_ne_zero 2 ?_
      exact Nat.factorial_ne_zero x

    apply sq_mul_x_is_sq this h1 hx_sq hy_sq

  obtain ⟨k, hk⟩ := this

  let n := x^2 + 5*x + 4

  have : IsSquare (n^2 + 2*n) := by
    have : n^2 + 2*n = (x+4)*(x+3)*(x+2)*(x+1) := by
      unfold n
      linarith
    rw [this, hk]
    exact IsSquare.mul_self k

  obtain ⟨r, hr⟩ := this
  rw [← Nat.pow_two r] at hr

  have hn_pos : 0 < n := by
    unfold n
    nlinarith

  have hlb : n^2 < r^2 := by
    rw [← hr]
    linarith

  have hub : r^2 < (n+1)^2 := by
    rw [← hr]
    linarith

  rw [Nat.pow_lt_pow_iff_left (by decide)] at hlb hub

  omega
