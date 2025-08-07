import Mathlib.Tactic
/-
OKTV 2016/2017, II. kategória, II. forduló, 2. feladat:

Igazoljuk, hogy ha x, y, és z eleme a [−5, 3] intervallumnak, akkor
√(3*x − 5*y − x*y + 15) + √(3*y − 5*z − y*z + 15) + √(3*z − 5*x − x*z + 15) ≤ 12.
Mikor áll fenn egyenlőség?
--------------------------------
igazoljuk az egyenlőtlenséget, majd bizonyítsuk hogy egyenlőség x=y=z=-1 esetben áll fent
-/
lemma amgm_ineq {a b : ℝ} (h1 : a ≥ 0) (h2 : b ≥ 0) : √(a*b) ≤ (a+b)/2 := by
  rw [Real.sqrt_le_left ?_]
  rw [div_pow _ 2 2]
  rw [le_div_iff₀ (by norm_num)]
  rw [add_pow_two]
  refine le_of_sub_nonneg ?_

  have :  a^2 + 2*a*b + b^2 - a*b*2^2 = (a-b)^2 := by ring
  rw [this]

  exact sq_nonneg (a - b)
  linarith

theorem oktv2016_ii_ii_ii (x y z : ℝ) (hxl : -5 ≤ x) (hxu : x ≤ 3) (hyl : -5 ≤ y) (hyu : y ≤ 3) (hzl : -5 ≤ z) (hzu : z ≤ 3) :
  √(3*x - 5*y - x*y + 15) + √(3*y - 5*z - y*z + 15) + √(3*z - 5*x - x*z + 15) ≤ 12 ∧ (√(3*x - 5*y - x*y + 15) + √(3*y - 5*z - y*z + 15) + √(3*z - 5*x - x*z + 15) = 12 ↔ (x=-1 ∧ y=-1 ∧ z=-1)) := by
  have : (3*x - 5*y - x*y + 15) = (x+5)*(3-y) := by ring_nf
  rw [this]

  have : (3*y - 5*z - y*z + 15) = (y+5)*(3-z) := by ring_nf
  rw [this]

  have : (3*z - 5*x - x*z + 15) = (z+5)*(3-x) := by ring_nf
  rw [this]

  have hxp5 : x+5 ≥ 0 := by exact neg_le_iff_add_nonneg.mp hxl
  have hyp5 : y+5 ≥ 0 := by exact neg_le_iff_add_nonneg.mp hyl
  have hzp5 : z+5 ≥ 0 := by exact neg_le_iff_add_nonneg.mp hzl
  have hxm3 : 3-x ≥ 0 := by exact sub_nonneg_of_le hxu
  have hym3 : 3-y ≥ 0 := by exact sub_nonneg_of_le hyu
  have hzm3 : 3-z ≥ 0 := by exact sub_nonneg_of_le hzu

  have h1 : √((x+5)*(3-y)) ≤ ((x+5)+(3-y))/2 := by exact amgm_ineq hxp5 hym3
  have h2 : √((y+5)*(3-z)) ≤ ((y+5)+(3-z))/2 := by exact amgm_ineq hyp5 hzm3
  have h3 : √((z+5)*(3-x)) ≤ ((z+5)+(3-x))/2 := by exact amgm_ineq hzp5 hxm3

  constructor
  · linarith
  · constructor
    · intro h
      by_contra!

      have hsq4 : √4 = 2 := by
            rw [Real.sqrt_eq_iff_mul_self_eq_of_pos (by norm_num)]
            norm_num

      have hsq16 : √16 = 4 := by
            rw [Real.sqrt_eq_iff_mul_self_eq_of_pos (by norm_num)]
            norm_num

      by_cases hx: x=-1
      · by_cases hy: y=-1
        · have hz : z ≠ -1 := by exact this hx hy
          rw [hx, hy] at h
          norm_num at h

          rw [hsq4, hsq16] at h

          have : √(3-z) + √(z+5) = 4 := by linarith
          rw [← sq_eq_sq₀ ?_] at this
          rw [add_pow_two] at this
          rw [Real.sq_sqrt hzp5] at this
          rw [Real.sq_sqrt hzm3] at this

          have : √(3 - z) * √(z + 5) = 4 := by linarith
          rw [← sq_eq_sq₀ ?_] at this
          rw [mul_pow] at this
          rw [Real.sq_sqrt hzm3, Real.sq_sqrt hzp5] at this

          have : (z+1)^2 = 0 := by nlinarith
          have : z+1=0 := by exact pow_eq_zero this
          have : z=-1 := by exact Eq.symm (neg_eq_of_add_eq_zero_left this)

          contradiction
          all_goals norm_num

          refine Left.mul_nonneg ?_ ?_
          exact Real.sqrt_nonneg (3 - z)
          exact Real.sqrt_nonneg (z + 5)

          refine Left.add_nonneg ?_ ?_
          exact Real.sqrt_nonneg (3 - z)
          exact Real.sqrt_nonneg (z + 5)
        · by_cases hz: z=1
          · rw [hx, hz] at h
            norm_num at h

            rw []
          · sorry
      · by_cases hy: y=1
        · by_cases hz: z=1
          · sorry
          · sorry
        · by_cases hz: z=1
          · sorry
          · sorry
    · intro h
      obtain ⟨rfl, rfl, rfl⟩ := h
      norm_num

      have : √16 = 4 := by exact (Real.sqrt_eq_iff_mul_self_eq_of_pos (by norm_num)).mpr (by norm_num)
      rw [this]
      norm_num

example {a b : ℝ } : a=b ↔ a^2=b^2 := by
  refine Iff.symm (sq_eq_sq₀ ?_ ?_)

example {a b c : ℝ} (h1 : a ≥ 0) (h2 : b ≠ 0) : c ≤ a/b ↔ c*b ≤ a := by
  refine le_div_iff₀ ?_
  sorry

example {a : ℝ} (h1 : a ≥ 0) : (√a)^2 = a := by exact Real.sq_sqrt h1
