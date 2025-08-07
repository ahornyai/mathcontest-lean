import Mathlib.Tactic

/-
Arany Dániel 2023/2024 Haladók I. kategória I. forduló I. feladat

Határozzuk meg azokat az a, b, c pozitív prímszámokat, amelyekre teljesül az alábbi egyenlőség.
a^2 + a*b + b^2 = c^2 + 3
-----
bizonyítsuk, hogy az egyetlen megoldás a=2 b=2 c=3
-/
theorem arany2023_advanced_i_i_i {a b c : ℕ} (ha : Nat.Prime a) (hb : Nat.Prime b) (hc : Nat.Prime c)
  : a^2 + a*b + b^2 = c^2 + 3 ↔ a=2 ∧ b=2 ∧ c=3 := by
  constructor
  · intro h

    by_cases h1: c=2
    · have : a ≥ 2 := by exact Nat.Prime.two_le ha
      have : b ≥ 2 := by exact Nat.Prime.two_le hb

      nlinarith
    · have hc_odd : Odd c := by exact Nat.Prime.odd_of_ne_two hc h1

      have rhs_even : Even (c^2 + 3) := by exact Odd.add_odd (Odd.pow hc_odd) (by decide)

      by_cases h2: a=2
      · by_cases h3: b=2
        · have : c=3 := by nlinarith
          exact ⟨h2, h3, this⟩
        · have : Odd b := by exact Nat.Prime.odd_of_ne_two hb h3
          have lhs_odd : ¬ Even (a ^ 2 + a * b + b ^ 2) := by
            rw[h2, Nat.not_even_iff_odd]
            refine Even.add_odd ?_ ?_

            have : 2 ^ 2 + 2 * b = 2*(2+b) := by ring
            rw [this]
            exact even_two_mul (2 + b)

            exact Odd.pow this

          rw [h] at lhs_odd
          contradiction
      · by_cases h3: b=2
        · have : Odd a := by exact Nat.Prime.odd_of_ne_two ha h2
          have lhs_odd : ¬ Even (a ^ 2 + a * b + b ^ 2) := by
            rw [Nat.not_even_iff_odd, h3, add_assoc]
            refine Even.odd_add ?_ ?_

            have : a*2+2^2 = 2*(a+2) := by ring
            rw [this]
            exact even_two_mul (a + 2)

            exact Odd.pow this

          rw [h] at lhs_odd
          contradiction
        · have ha_odd : Odd a := by exact Nat.Prime.odd_of_ne_two ha h2
          have hb_odd : Odd b := by exact Nat.Prime.odd_of_ne_two hb h3
          have lhs_odd : ¬ Even (a ^ 2 + a * b + b ^ 2) := by
            rw [Nat.not_even_iff_odd]
            refine Even.add_odd ?_ ?_
            refine Odd.add_odd ?_ ?_

            exact Odd.pow ha_odd
            exact Odd.mul ha_odd hb_odd
            exact Odd.pow hb_odd

          rw [h] at lhs_odd
          contradiction
  · intro h
    obtain ⟨rfl, rfl, rfl⟩ := h
    norm_num
