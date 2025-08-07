import Mathlib.Tactic

/-
Arany Dániel 2023/2024 Haladók I. kategória II. forduló I. feladat

Milyen pozitív egész a, b, c értékekre teljesülnek a
2*a/(2 + a) = 3*b/(3 + b) = 4*c/(4 + c)
egyenlőségek?
-----
bizonyítsuk, hogy az egyetlen megoldás: a=12, b=4, c=3
-/
theorem arany2023_advanced_i_ii_i {a b c : ℤ} (hapos: a > 0) (hbpos : b > 0) (hcpos : c > 0)
  : (2*a/(2 + a) = (3*b/(3 + b) : ℚ) ∧ 3*b/(3 + b) = (4*c/(4 + c) : ℚ)) ↔ a=12 ∧ b=4 ∧ c=3 := by
  constructor
  · intro h
    obtain ⟨h1, h2⟩ := h

    have ha_div_neq_0 : 2+a ≠ 0 := by linarith
    have hc_div_neq_0 : 4+c ≠ 0 := by linarith
    have h3 : (a+4)*(c-4) = -16 := by
      rw [← h1] at h2
      field_simp at h2
      norm_cast at h2
      linarith

    have : c < 4 := by
      by_contra!
      have hcontra : (a+4)*(c-4) ≥ 0 := by exact Int.mul_nonneg (by linarith) (by linarith)
      linarith

    interval_cases c
    · omega
    · have : a=4 := by linarith
      have : 5*b=12 := by
        rw [this] at h1
        field_simp at h1
        norm_num at h1
        norm_cast at h1
        linarith

      have h4 : 5 ∣ (12 : ℤ) := by exact Dvd.intro b this

      contradiction
    · have ha : a=12 := by linarith
      have hb : b=4 := by
        rw [ha] at h1
        field_simp at h1
        norm_num at h1
        norm_cast at h1
        linarith

      exact ⟨ha, hb, rfl⟩
  · intro h
    obtain ⟨rfl, rfl, rfl⟩ := h
    norm_num

example {a b c d : ℚ} (hc : c ≠ 0) (hd : d ≠ 0) : a = b/d ↔ a*d=b := by
  rw [eq_div_iff]
