import Mathlib.Tactic
import Mathlib.Algebra.Group.Even

/-
OKTV 2022/2023, II. kategória, II. forduló, 4. feladat:

Melyik az a legnagyobb x egész szám, amelyre 4^17 + 4^1020 + 4^x négyzetszám?
-/

noncomputable abbrev max_x : ℕ := 2022
noncomputable abbrev max_k : ℕ := Nat.sqrt (4 ^ 17 + 4 ^ 1020 + 4 ^ max_x)

abbrev IsGood (x : ℕ) : Prop := IsSquare (4^17 + 4^1020 + 4^x)

set_option exponentiation.threshold 2023

lemma sq_mul_x_is_sq {a x b : ℕ} (ha : a ≠ 0) (hb : b ≠ 0) (h : a*x = b) (ha_sq : IsSquare a) (hb_sq : IsSquare b) :
  IsSquare x := by {
  rcases ha_sq with ⟨c, rfl⟩
  rcases hb_sq with ⟨d, rfl⟩

  -- a = c^2 és b = d^2
  have h1 : c^2 * x = d^2 := by linarith

  -- Most megmutatjuk, hogy d osztható c-vel
  have h_div_sq : c^2 ∣ d^2 := by exact Dvd.intro x h1

  have h_div : c ∣ d := by {
    rw [Nat.pow_dvd_pow_iff] at h_div_sq

    exact h_div_sq
    norm_num
  }

  -- Legyen d = c * k valamilyen k-ra
  rcases h_div with ⟨k, hk⟩
  subst hk

  -- Most átrendezzük a jobb oldalt
  have h2 : c * c * x = c * c * (k * k) := by {
    rw [h]
    ring
  }

  have h3 : x = k * k := by {
    have hc2 : c * c > 0 := by omega

    apply Nat.eq_of_mul_eq_mul_left hc2
    exact h2
  }

  use k
}

theorem oktv_2022_ii_4 : IsGreatest { x : ℕ | IsGood x } max_x := by {
    unfold IsGreatest IsGood max_x upperBounds IsSquare
    constructor
    · use max_k
      norm_num
    · simp only [Set.mem_setOf_eq]
      intro x
      contrapose!
      intro he k h₁

      /-
      Tegyük fel, hogy x > 2022, a kifejezés mégis négyzetszám. Ekkor kiemelhetünk 4^17
      -/
      have h₂ : 4^17 + 4^1020 + 4^x = 4^17 * (1 + 4^1003 + 4^(x-17)) := by {
          have h_factor2 : 4^x = 4^17 * 4^(x-17) := by {
            rw [← pow_add]
            norm_num
            omega
          }

          calc
            _ = 4^17 + 4^17 * 4^1003 + 4^17 * 4^(x-17) := by rw [← pow_add, h_factor2]
            _ = 4^17 * (1 + 4^1003 + 4^(x-17)) := by ring
      }

      rw [h₂] at h₁

      /-
      Mivel 4^17 négyzetszám, ezért 1 + 4^1003 + 4^(x−17) is az.
      -/
      have h417_sq : IsSquare (4^17) := by {
        use 2^17
        norm_num
      }

      have h417_neq_0 : 4^17 ≠ 0 := by norm_num

      have hk_neq_0 : k ≠ 0 := by {
        by_contra hk_zero
        rw [hk_zero] at h₁
        simp at h₁
      }

      have hk_sq_neq_0 : k * k ≠ 0 := by exact Nat.mul_ne_zero hk_neq_0 hk_neq_0

      have h_is_square : IsSquare (1 + 4^1003 + 4^(x-17)) := by
        apply sq_mul_x_is_sq
        · exact h417_neq_0
        · exact hk_sq_neq_0
        · exact h₁
        · exact h417_sq
        · use k

      have eq_4x_17_2x_17_sq : 4^(x-17) = (2^(x-17))^2 := by {
        calc
          _ = 2^(2*(x-17))    := by exact Eq.symm (Mathlib.Tactic.Ring.pow_nat rfl rfl rfl)
          _ = (2^(x-17)) ^ 2  := by exact Nat.pow_mul' 2 2 (x - 17)
      }

      have h_exp_simplify : 2 * 2^(x-17) = 2^(x-16) := by {
        have h2 : 2 * 2^(x-17) = 2^(1 + (x-17)) := by exact Eq.symm (Nat.pow_add 2 1 (x - 17))
        rw [h2]

        have h3 : 1 + (x-17) = x-16 := by omega
        rw [h3]
      }

      have h_is_gt_2x_17_sq : 1 + 4^1003 + 4^(x-17) > (2^(x-17))^2 := by omega

      unfold IsSquare at h_is_square
      rcases h_is_square with ⟨r, h_req⟩

      have h_r_sq_is_gt_2x_17_sq : r^2 > (2^(x-17))^2 := by {
        rw [← Nat.pow_two] at h_req
        exact Nat.lt_of_lt_of_eq h_is_gt_2x_17_sq h_req
      }

      have h_r_gt_2x_17 : r > 2^(x-17) := by exact lt_of_pow_lt_pow_left' 2 h_r_sq_is_gt_2x_17_sq

      have h_is_geq_1_plus_2x_17_sq : 1 + 4^1003 + 4^(x-17) ≥ (2^(x-17) + 1)^2 := by {
        rw [h_req]
        rw [← Nat.pow_two]
        exact Nat.pow_le_pow_of_le_left h_r_gt_2x_17 2
      }

      have h_x_leq_2022 : x ≤ 2022 := by {
        have : x - 16 ≤ 2006 ↔ x ≤ 2022 := Nat.sub_le_iff_le_add
        rw [← this]

        have : 2^(x-16) ≤ 2^2006 ↔ x - 16 ≤ 2006 := by {
          refine Nat.pow_le_pow_iff_right ?_
          norm_num
        }
        rw [← this]

        have : 4^1003 = 2^2006 := by norm_num
        rw [← this]

        have : 1 + 2 ^ (x - 16) + 4^(x-17) ≤ 1 + 4 ^ 1003 + 4^(x-17) ↔ 2^(x-16) ≤ 4^1003 := by omega
        rw [← this]

        linarith
      }

      omega
}
