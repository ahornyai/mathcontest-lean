import Mathlib.Tactic
/-
OKTV 2018/2019, I. kategória, II. forduló, 4. feladat:

Oldja meg a következő egyenletet a valós számok halmazán:
1 + 1/(1 + 1/(1 + 1/(Real.logb x 2))) = Real.logb (4*x) (9*x-1)
--------------------------------
bizonyítsuk be, hogy az egyetlen megoldás az x=1/8
-/
lemma logb_inv {a b : ℝ} (h1 : a > 0) (h2 : a ≠ 1) (h3 : b > 0) (h4 : b ≠ 1) : Real.logb a b = 1/(Real.logb b a) := by
  unfold Real.logb

  have : Real.log a ≠ 0 := by
    exact Real.log_ne_zero_of_pos_of_ne_one h1 h2

  have : Real.log b ≠ 0 := by
    exact Real.log_ne_zero_of_pos_of_ne_one h3 h4

  field_simp

lemma logb_add_one {a b : ℝ} (h1 : a > 0) (h2 : a ≠ 1) (h3 : b ≠ 0) : 1 + Real.logb a b = Real.logb a (a*b) := by
  have : Real.logb a a = 1 := by
    refine Real.logb_self_eq_one_iff.mpr ?_
    refine And.symm ⟨?_, ?_⟩
    refine And.symm ⟨?_, ?_⟩
    linarith
    exact h2
    linarith
  rw [← this]
  refine Eq.symm (Real.logb_mul ?_ ?_)

  exact Ne.symm (ne_of_lt h1)
  exact h3

lemma logb_inj_a_gt_1 {a b c : ℝ} (h1 : a > 1) (h2 : b > 0) (h3 : c > 0) : Real.logb a b = Real.logb a c ↔ b=c := by
  have hlog_inj : Set.InjOn (Real.logb a) (Set.Ioi 0) := by
    refine Real.logb_injOn_pos ?_
    exact h1

  apply hlog_inj.eq_iff
  all_goals
    refine Set.mem_Ioi.mpr ?_
    linarith

lemma logb_inj_a_lt_1 {a b c : ℝ} (h1 : a > 0) (h2 : a < 1) (h3 : b > 0) (h4 : c > 0) : Real.logb a b = Real.logb a c ↔ b=c := by
  have hlog_inj : Set.InjOn (Real.logb a) (Set.Ioi 0) := by
    exact Real.logb_injOn_pos_of_base_lt_one h1 h2

  apply hlog_inj.eq_iff
  all_goals
    refine Set.mem_Ioi.mpr ?_
    linarith

theorem oktv_2018_i_ii (x : ℝ) (h1 : x > 1/9) (h2 : x ≠ 1/4) (h3 : x ≠ 1/2) (h4 : x ≠ 1)
  : 1 + 1/(1 + 1/(1 + 1/(Real.logb x 2))) = Real.logb (4*x) (9*x-1) ↔ x=1/8 := by
  have h2x2_neq_1 : 2*x*2 ≠ 1 := by
    by_contra!
    have : x=1/4 := by linarith
    rw [this] at h2
    contradiction

  have h2x_neq_1 : 2*x ≠ 1 := by
    by_contra!
    have : x=1/2 := by linarith
    rw [this] at h2
    contradiction

  constructor
  · intro h
    repeat rw [← logb_inv, logb_add_one] at h

    have : 2 * x * 2 = 4*x := by ring_nf
    rw [this] at h

    have hquad : 4 * x * (2 * x) = 9 * x - 1 → x=1/8 := by
      intro h'

      have : (x-1)*(x-1/8) = 0 := by linarith
      have : x-1=0 ∨ x-1/8=0 := by exact mul_eq_zero.mp this

      rcases this with h5 | h5
      · have : x=1 := by linarith
        contradiction
      · linarith

    by_cases h': 4*x>1
    · rw [logb_inj_a_gt_1] at h

      apply hquad at h
      exact h
      exact h'
      nlinarith
      linarith
    · have h5 : 4*x ≤ 1 := by linarith
      have h4x_neq_1 : 4*x ≠ 1 := by
        by_contra!
        have : x=1/4 := by linarith
        rw [this] at h2
        contradiction
      have : 4*x < 1 := by exact lt_of_le_of_ne h5 h4x_neq_1
      rw [logb_inj_a_lt_1] at h

      apply hquad at h
      exact h
      linarith
      linarith
      nlinarith
      linarith

    linarith
    exact h2x2_neq_1
    repeat linarith
    exact h2x2_neq_1
    linarith
    exact h2x_neq_1
    linarith
    exact h2x_neq_1
    norm_num
    linarith
    exact h2x_neq_1
    repeat norm_num
    linarith
    repeat norm_num
    linarith
    exact h4
  · intro h
    rw [h]
    repeat rw [← logb_inv, logb_add_one]
    repeat norm_num
