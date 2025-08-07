import Mathlib.Tactic

/-
Arany Dániel 2021/2022 Haladók II. kategória II. forduló II. feladat

Oldjuk meg a valós számok halmazán az alábbi egyenletet!
x = √(x - 1/x) + √(1 - 1/x)
----------------------------
Bizonyítsuk, hogy az egyetlen megoldás a x = (1+√5)/2
-/
theorem arany2021_A_ii_ii_ii (x : ℝ) (hx_geq_1 : x ≥ 1) : x = √(x - 1/x) + √(1 - 1/x) ↔ x = (1+√5)/2 := by
  constructor
  · intro h

    rw [← sq_eq_sq₀ (by linarith) (by linarith)] at h
    rw [add_pow_two] at h
    repeat rw [Real.sq_sqrt] at h

    have h1sq_nonneg : 0 ≤ 1 - 1 / x := by
      refine sub_nonneg_of_le ?_
      exact (div_le_iff₀' (by linarith)).mpr (by linarith)

    have h2sq_nonneg : 0 ≤ x - 1 / x := by
      refine sub_nonneg_of_le ?_
      exact (div_le_iff₀' (by linarith)).mpr (by nlinarith)

    have : √(x - 1 / x) * √(1 - 1 / x) = √((x^3 - x^2 - x + 1)/(x^2)) := by
      rw [← Real.sqrt_mul']

      have : ((x - 1 / x) * (1 - 1 / x)) = ((x ^ 3 - x ^ 2 - x + 1) / x ^ 2) := by
        field_simp
        ring
      rw [this]

      exact h1sq_nonneg

    rw [mul_assoc, this] at h
    rw [Real.sqrt_div', Real.sqrt_sq] at h
    field_simp at h

    let u := √(x^3 - x^2 - x + 1)

    have hsq_nonneg : 0 ≤ x ^ 3 - x ^ 2 - x + 1 := by
      have : x ^ 3 - x ^ 2 - x + 1 = x^2 * (x - 1 / x) * (1 - 1 / x) := by
        field_simp
        ring
      rw [this]

      refine mul_nonneg ?_ h1sq_nonneg
      exact mul_nonneg (sq_nonneg x) h2sq_nonneg

    have h₁ : (u-1)^2 = 0 := by
      unfold u
      rw [sub_pow_two, Real.sq_sqrt]
      linarith
      exact hsq_nonneg

    have h₂ : u=1 := by nlinarith

    have h₃ : x = 0 ∨ x = (1-√5)/2 ∨ x = (1 + √5)/2 := by
      unfold u at h₂
      rw [Real.sqrt_eq_iff_eq_sq (hsq_nonneg) (by norm_num)] at h₂

      have : x*(x^2 - x - 1) = 0 := by nlinarith
      simp at this

      rcases this with h₃ | h₃
      · left
        exact h₃
      · have : (x - ((1-√5)/2)) * (x - ((1 + √5)/2)) = 0 := by
          have : (√5)^2 = 5 := by exact Real.sq_sqrt (by norm_num)
          nlinarith
        simp at this
        right

        rcases this with h₄ | h₄
        · left
          linarith
        · right
          linarith

    rcases h₃ with h₄ | h₄ | h₄
    · linarith
    · have : (1 - √5)/2 < 0 := by
        refine div_neg_of_neg_of_pos ?_ (by norm_num)
        refine sub_neg.mpr ?_
        exact Real.lt_sqrt_of_sq_lt (by norm_num)

      linarith
    · exact h₄

    nlinarith
    nlinarith
  · intro h
    rw [h]
    sorry
