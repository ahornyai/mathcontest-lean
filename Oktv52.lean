import Mathlib.Tactic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Complex

lemma abs_negone_pow_eq_one {k : ℤ} : (|(-1) ^ k| : ℝ) = 1 := by
  by_cases h : Even k
  · obtain ⟨m, hm⟩ := h
    rw [← two_mul] at hm
    rw [hm, zpow_mul, zpow_two]
    simp
  · have hodd : Odd k := by exact Int.not_even_iff_odd.mp h
    obtain ⟨m, hm⟩ := hodd

    have : ((-1) : ℝ)^k = -1 := by
      rw [zpow_eq_neg_one_iff₀]

      exact ⟨rfl, (by exact Int.not_even_iff_odd.mp h)⟩

    rw [this]
    simp

/-
OKTV 2015/2016, I. kategória, II. forduló, 3. feladat:

Bizonyítsa be, hogy mindeny valós szám esetén 2 * |sin x| + 3 * |cos x| ≥ 2
Mikor áll fenn egyenlőség?
----
Az egyenlőség ∀ k: ℤ, x = π/2 + k * π esetén áll fent.
-/
theorem oktv_2015_i_iii {x : ℝ} : 2 * |Real.sin x| + 3 * |Real.cos x| ≥ 2 
  ∧ (2 * |Real.sin x| + 3 * |Real.cos x| = 2 ↔ ∃ k: ℤ, x = Real.pi/2 + k * Real.pi) := by
  have h₁ : |Real.sin x| ≥ (Real.sin x)^2 := by
    rw [← sq_abs (Real.sin x)]
    apply sq_le

    exact abs_nonneg (Real.sin x)
    exact Real.abs_sin_le_one x
  
  have h₂ : |Real.cos x| ≥ (Real.cos x)^2 := by
    rw [← sq_abs (Real.cos x)]
    apply sq_le

    exact abs_nonneg (Real.cos x)
    exact Real.abs_cos_le_one x
  
  have h₃ : 2 * |Real.sin x| + 3 * |Real.cos x| ≥ 2 + (Real.cos x)^2 := by
    have : 2 * |Real.sin x| + 3 * |Real.cos x| ≥ 2 * ((Real.sin x)^2 + (Real.cos x)^2) + (Real.cos x)^2 := by linarith
    simp at this
    exact this

  constructor
  · exact le_of_add_le_of_nonneg_left h₃ (sq_nonneg (Real.cos x))
  · constructor
    · intro h
      rw [← sq_eq_sq₀, add_pow_two] at h

      have : 4 * ((|Real.sin x|)^2 + (|Real.cos x|)^2) + 5 * |Real.cos x|^2 + 12*|Real.sin x| * |Real.cos x| = 4 := by
        linarith

      have : 5 * (Real.cos x)^2 + 12*|Real.sin x| * |Real.cos x| = 0 := by
        simp at this
        linarith

      have h₄ : Real.cos x = 0 := by nlinarith
      rw [Real.cos_eq_zero_iff] at h₄

      obtain ⟨k, hk⟩ := h₄
      use k

      all_goals linarith
    · intro h
      obtain ⟨k, hk⟩ := h
      rw [hk, Real.sin_add_int_mul_pi, Real.cos_add_int_mul_pi]
      simp
      exact abs_negone_pow_eq_one
