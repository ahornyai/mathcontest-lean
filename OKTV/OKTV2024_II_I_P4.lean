import Mathlib.Tactic
import Mathlib.Algebra.Group.Even

/-
OKTV 2024/2025, II. kategória, I. forduló, 4. feladat:

Oldjuk meg az alábbi egyenletet, amelynek változói pozitív egész számok lehetnek:
15(abc + a + c) = 2024(bc + 1)
-/
theorem eq_of_mul_eq_fourteen {x y : ℕ} (h : x * y = 14) :
    x = 1 ∧ y = 14 ∨ x = 2 ∧ y = 7 ∨ x = 7 ∧ y = 2 ∨ x = 14 ∧ y = 1 := by
  have h₁ : (x, y) ∈ Nat.divisorsAntidiagonal 14 := by simpa using h
  have h₂ : Nat.divisorsAntidiagonal 14 = {(1, 14), (2, 7), (7, 2), (14, 1)} := by rfl
  simpa [h₂] using h₁

theorem oktv_2024_ii_i_iv {a b c : ℕ} (apos : a > 0) (bpos : b > 0) (cpos : c > 0)
  : 15 * (a * b * c + a + c) = 2024 * (b * c + 1) ↔ (a, b, c) = (134, 1, 14) := by
    constructor
    · intro heq
      have h1 : (2024 - 15 * a) * (b * c + 1) = 15 * c := by
        calc
          _ = 2024 * (b * c + 1) - 15 * a * (b * c + 1)                     := by rw [Nat.mul_sub_right_distrib]
          _ = 15 * (a * b * c + a + c) - 15 * a * (b * c + 1)               := by rw [heq]
          _ = 15 * a * b * c + 15 * a + 15 * c - (15 * a * b * c + 15 * a)  := by ring_nf
          _ = 15 * c                                                        := by simp

      --  Mivel a heq egyenletben a bal oldal 15-el osztható, ezért a jobb oldal is osztható lesz 15-el.
      have hright_div_15 : 15 ∣ (2024 * (b * c + 1)) := by rw [←heq]; exact dvd_mul_right 15 _

      -- Tehát b * c + 1 osztható 15-tel, mert 2024 relatív prím 15-el.
      have hbc1_div_15 : 15 ∣ (b * c + 1) := by apply Nat.Coprime.dvd_of_dvd_mul_left _ hright_div_15; exact rfl

      -- Ugyanakkor 15 osztható (b * c + 1) kifejezéssel
      -- 15 * (b * c + 1) osztható (b * c + 1)
      have h15bc1_div_bc1: (b * c + 1) ∣ 15 * (b * c + 1) := by exact Nat.dvd_mul_left (b * c + 1) 15

      -- 15 * c osztható (b * c + 1)
      have h15c_div_bc1: (b * c + 1) ∣ 15 * c := by rw [← h1]; exact Nat.dvd_mul_left (b * c + 1) (2024 - 15 * a)

      -- 15 * b * c osztható (b * c + 1)
      have h15bc_div_bc1: (b * c + 1) ∣ 15 * b * c := by
        apply Nat.dvd_trans h15c_div_bc1
        apply Nat.mul_dvd_mul_right ?_ c
        exact Nat.dvd_mul_right 15 b

      -- Mivel mind a két feltétel teljesül, ezért be tudjuk bizonyítani, hogy b * c + 1 | 15
      have h15_div_bc1: (b * c + 1) ∣ 15 := by
        -- (b * c + 1) osztja 15 * (b * c + 1) - 15 * b * c
        have h2 : (b * c + 1) ∣ (15 * (b * c + 1) - 15 * b * c) := by
          apply Nat.dvd_sub ?_ ?_

          exact h15bc1_div_bc1
          exact h15bc_div_bc1

        -- De ez pontosan 15-et ad: 15 * (b * c + 1) - 15 * b * c = 15
        have h3 : 15 * (b * c + 1) - 15 * b * c = 15 := by apply Nat.sub_eq_of_eq_add ?_; ring;

        -- Tehát (b * c + 1) osztója 15-nek
        rw [h3] at h2
        exact h2

      -- ha b * c + 1 osztható 15-tel és 15 osztható b * c + 1-gyel, akkor b * c + 1 = 15
      have hbc1_eq_15: b * c + 1 = 15 := by exact Eq.symm (Nat.dvd_antisymm hbc1_div_15 h15_div_bc1)

      -- Tehát b * c = 14 - exist? ftw
      have hbc_eq_14: b * c = 14 := by linarith

      -- nézzük meg az összes lehetséges b és c értéket, amelyekre b * c = 14
      rcases eq_of_mul_eq_fourteen hbc_eq_14 with (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩)

      -- ha b = 1 és c = 14, akkor a = 134
      refine Prod.mk_inj.mpr ?_
      refine ⟨?_, rfl⟩
      linarith

      -- más esetekben ellentmondásra jutunk
      all_goals omega
    · intro h
      obtain ⟨rfl, rfl, rfl⟩ := h
      norm_num
