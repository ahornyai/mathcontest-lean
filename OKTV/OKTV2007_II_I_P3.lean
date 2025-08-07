import Mathlib.Tactic
import Mathlib.Algebra.Group.Even

/-
OKTV 2007/2008, II. kategória, I. forduló, 3. feladat:

Határozzuk meg, mely a és b egész számokra igaz:
b/(a-1) + (a-4)/(b+1) = 1
-/
def SolutionSet : Set (ℤ × ℤ) := {(4, 3), (5, 0), (5, 3)}

theorem oktv2007_ii_i_iii (a b : ℤ) (ha_neq_one : a ≠ 1) (hb_neq : b ≠ -1) : ⟨a, b⟩ ∈ SolutionSet ↔ (b/(a-1) + (a-4)/(b+1) : ℚ) = 1 := by
  unfold SolutionSet
  constructor
  · intro h
    simp at h

    rcases h with h | h | h
    all_goals
      obtain ⟨rfl, rfl⟩ := h
      norm_num
  · intro h

    have ham1_neq_q : (a-1 : ℚ) ≠ 0 := by
      refine sub_ne_zero.mpr ?_
      exact Int.cast_ne_one.mpr ha_neq_one

    have hbp1_neq_q : (b+1 : ℚ) ≠ 0 := by
      by_contra!
      have : (b : ℚ) = -1 := by linarith
      norm_cast at this

    have : ((a-1)*(b+1) : ℚ) ≠ 0 := by
      refine mul_ne_zero_iff.mpr ?_
      exact ⟨ham1_neq_q, hbp1_neq_q⟩

    rw [← mul_eq_right₀ this] at h
    field_simp at h

    have : (b^2 + b + a^2 - 5*a + 4 : ℚ) = a*b + a - b - 1 := by linarith
    norm_cast at this

    have : 1*b*b + (2-a)*b + (a^2 - 6*a + 5) = 0 := by linarith

    by_cases h': 1 < a ∧ a < 6
    · obtain ⟨hl, hu⟩ := h'

      interval_cases a
      · have : b^2 = 3 := by linarith
        have h1: IsSquare (3 : ℤ) := by
          refine (isSquare_iff_exists_sq 3).mpr ?_
          use b
          exact id (Eq.symm this)

        have h1_contra: ¬ IsSquare (3 : ℤ) := by
          refine Prime.not_square ?_
          exact Int.prime_three

        contradiction
      · have h1 : 1*(b*b) + (-1)*b + (-4) = 0 := by linarith
        have h2 : discrim 1 (-1) (-4) = 17 := by rfl
        have h3 : ∀ s, discrim 1 (-1) (-4) ≠ s^2 := by
          by_contra!
          rw [h2] at this

          have : IsSquare (17 : ℤ) := by
            refine (isSquare_iff_exists_sq 17).mpr ?_
            obtain ⟨s, hs⟩ := this
            use s
          have : ¬ IsSquare (17 : ℤ) := by
            refine Prime.not_square ?_
            norm_num

          contradiction

        have : 1 * (b * b) + -1 * b + -4 ≠ 0 := quadratic_ne_zero_of_discrim_ne_sq h3 b

        contradiction
      · have : (b-3)*(b+1) = 0 := by linarith
        have : b-3 = 0 ∨ b+1 = 0 := by exact Int.mul_eq_zero.mp this

        rcases this with h1 | h1
        · have : b=3 := by linarith
          rw [this]
          exact Set.mem_insert (4, 3) {(5, 0), (5, 3)}
        · omega
      · have : b*(b-3) = 0 := by linarith
        have : b = 0 ∨ b-3 = 0 := by exact Int.mul_eq_zero.mp this

        rcases this with h | h
        · rw [h]
          norm_num
        · have : b=3 := by linarith
          rw [this]
          norm_num
    · have : ¬ (1 < a) ∨ ¬ (a < 6) := by exact Decidable.not_and_iff_or_not.mp h'
      push_neg at this

      rcases this with h1 | h1
      · have h1 : a < 1 := by omega
        have : 1*b*b + (2-a)*b + (a^2 - 6*a + 5) ≠ 0 := by nlinarith

        omega
      · have : 1*(b*b) + (2-a)*b + (a^2 - 6*a + 5) ≠ 0 := by
          have : discrim 1 (2-a) (a^2 - 6*a + 5) = (2-a)^2 - 4*1*(a^2 - 6*a + 5) := rfl
          have h2 : discrim (1) (2-a) (a^2 - 6*a + 5) < 0 := by nlinarith
          have h3 : ∀ s, discrim (1) (2-a) (a^2 - 6*a + 5) ≠ s^2 := by
            by_contra!
            obtain ⟨s, hs⟩ := this
            have : s^2 ≥ 0 := by exact sq_nonneg s
            have : s^2 < 0 := by linarith

            omega

          exact quadratic_ne_zero_of_discrim_ne_sq h3 b
        rw [←mul_assoc] at this

        contradiction
