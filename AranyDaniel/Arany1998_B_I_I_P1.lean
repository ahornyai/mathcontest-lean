import Mathlib.Tactic

/-
Arany Dániel 1998/1999 Kezdők I. kategória I. forduló I. feladat

Mi lehet az a természetes szám, amely négyzetszám lesz, ha hozzáadunk 5-öt, de négyzetszám lesz akkor is, ha elveszünk belőle 11-et?
_-----------------------------------
Bizonyítsuk, hogy két ilyen szám létezik, a 11 és a 20
-/
lemma eq_of_mul_eq_16 {x y : ℕ} (hx_geq_y : x ≥ y) (h : x * y = 16) :
    x = 16 ∧ y = 1 ∨ x = 8 ∧ y = 2 ∨ x = 4 ∧ y = 4 := by
  have h₁ : (x, y) ∈ Nat.divisorsAntidiagonal 16 := by simpa using h
  have h₂ : Nat.divisorsAntidiagonal 16 = {(1, 16), (2, 8), (4, 4), (8, 2), (16, 1)} := by rfl

  have : x = 1 ∧ y = 16 ∨ x = 2 ∧ y = 8 ∨ x = 4 ∧ y = 4 ∨ x = 8 ∧ y = 2 ∨ x = 16 ∧ y = 1 := by
    simpa [h₂] using h₁

  rcases this with h₃ | h₃ | h₃ | h₃ | h₃ <;> omega

theorem arany1998_beginner_i_i_i (x : ℕ) (hx_geq_11 : x ≥ 11) : (IsSquare (x+5) ∧ IsSquare (x-11)) ↔ x = 11 ∨ x = 20 := by
  constructor
  · intro h
    obtain ⟨h₁, h₂⟩ := h

    obtain ⟨k, hk⟩ := h₁
    obtain ⟨m, hm⟩ := h₂

    have h : k^2 - m^2 = 16 := by
      simp [Nat.pow_two]
      omega
    rw [Nat.sq_sub_sq] at h

    apply eq_of_mul_eq_16 (by omega) at h

    rcases h with h | h | h
    · omega
    · obtain ⟨h₁, h₂⟩ := h

      have : k=5 := by omega
      rw [this] at hk

      omega
    · obtain ⟨h₁, h₂⟩ := h

      have : k=4 := by omega
      rw [this] at hk

      omega
  · intro h
    rcases h with rfl | rfl <;> decide
