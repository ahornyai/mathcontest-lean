import Mathlib.Tactic

/-
Arany Dániel 2020/2021 Kezdők I. kategória II. forduló 1. feladat

Határozzuk meg az összes olyan n pozitív egész számot, amelynek létezik három olyan a > b > c
pozitív osztója, hogy a^2 - b^2, b^2 - c^2, a^2 - c^2 is osztója n-nek

Határozzuk meg az összes pozitív egész n számot, amely esetén 4*n^2 + 3*n + 7 négyzetszám
-/
theorem arany2021_i_ii_i (n : ℕ) (hnpos : n > 0) : IsSquare (4*n^2 + 3*n + 7) ↔ n=6 := by
  constructor
  · intro h

    have hlb : (2*n)^2 < 4 * n ^ 2 + 3 * n + 7 := by linarith
    have hub : 4 * n ^ 2 + 3 * n + 7 < (2*n+2)^2 := by linarith

    obtain ⟨k, hk⟩ := h
    rw [← pow_two k] at hk

    rw [hk] at hlb hub

    rw [Nat.pow_lt_pow_iff_left (by decide)] at hlb
    rw [Nat.pow_lt_pow_iff_left (by decide)] at hub
    
    nlinarith
  · intro h
    rw [h]
    use 13
    rfl
