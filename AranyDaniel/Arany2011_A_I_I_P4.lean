import Mathlib.Tactic

/-
Arany Dániel 2011/2012 Haladók I. kategória, I. forduló IV. feladat

Bizonyítsuk be, hogy 13^n + 3*5^(n-1) + 8 minden pozitív egész n esetén osztható 24-gyel!
-/
theorem arany2011_advanced_i_i_iv (n : ℕ) (hnpos : n > 0) : 24 ∣ 13^n + 3*5^(n-1) + 8 := by
  induction n with
  | zero => contradiction
  | succ n ih =>
    by_cases h: n=0
    · rw [h]
      rfl
    · have h2 : 13 ^ (n + 1) + 3 * 5 ^ (n + 1 - 1) + 8 = 13 * (13^n + 3*5^(n-1) + 8) - 8*3*5^(n-1) - 12*8 := by
        have : 5 ^ (n + 1 - 1) = 5*5^(n-1) := by exact Eq.symm (mul_pow_sub_one h 5)
        rw [this, Nat.pow_succ]

        omega

      omega
