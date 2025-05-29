import Mathlib.Tactic

/-
Arany Dániel 2011/2012 Kezdők I. kategória, I. forduló III. feladat

Mely x és y pozitív egész számokra igaz az alábbi egyenlőség?
x^2 - y^2 + 2*x - 6*y - 25 = 0
----------------------
Bizonyítsuk, hogy az egyetlen megoldás az x=8 ∧ y=5 páros
-/
lemma eq_of_mul_eq_17 {x y : ℤ} (hxpos : x > 0) (hypos : y > 0) (h : x * y = 17) :
    x = 1 ∧ y = 17 ∨ x = 17 ∧ y = 1 := by
  have x_nat : ∃ n : ℕ, x = n := by refine Int.eq_ofNat_of_zero_le (by exact Int.le_of_lt hxpos)
  have y_nat : ∃ n : ℕ, y = n := by refine Int.eq_ofNat_of_zero_le (by exact Int.le_of_lt hypos)

  obtain ⟨x, rfl⟩ := x_nat
  obtain ⟨y, rfl⟩ := y_nat
  norm_cast at *

  have h₁ : (x, y) ∈ Nat.divisorsAntidiagonal 17 := by simpa using h
  have h₂ : Nat.divisorsAntidiagonal 17 = {(1, 17), (17, 1)} := by rfl
  simpa [h₂] using h₁

theorem arany2011_beginner_i_i_iii (x y : ℤ) (hxpos: x > 0) (hypos : y > 0) : x^2 - y^2 + 2*x - 6*y - 25 = 0 ↔ x=8 ∧ y=5 := by
  constructor
  · intro h
    have : (x+y+4)*(x-y-2) = 17 := by linarith

    have : ((x+y+4) = 1 ∧ (x-y-2) = 17) ∨ ((x+y+4) = 17 ∧ (x-y-2) = 1) := by 
      exact eq_of_mul_eq_17 (by linarith) (by nlinarith) this
    
    rcases this with h1 | h1 <;> omega
  · intro h
    obtain ⟨rfl, rfl⟩ := h
    norm_num
