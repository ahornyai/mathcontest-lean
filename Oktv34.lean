import Mathlib.Tactic
/-
OKTV 2014/2015, I. kategória, I. forduló, 4. feladat:

Oldja meg a valós számok halmazán az
log₅(x+4) * log₅(x-1) = log₅((x+4)^2*(x-1)) - 2
egyenletet!
----
bizonyítsuk be, hogy az egyetlen megoldás az x=26
-/
theorem oktv_2014_i_iv (x : ℝ) (h1 : x > 1) : (Real.logb 5 (x+4)) * (Real.logb 5 (x-1)) = (Real.logb 5 ((x+4)^2 * (x-1))) - 2 ↔ x=26 := by
  constructor
  · intro h
    rw [Real.logb_mul, Real.logb_pow] at h
    norm_cast at h

    let a := Real.logb 5 (x+4)
    let b := Real.logb 5 (x-1)

    have h2 : (a-1)*(b-2) = 0 := by linarith
    have : a-1 = 0 ∨ b-2 = 0 := by exact mul_eq_zero.mp h2

    have hlog_inj : Set.InjOn (Real.logb 5) (Set.Ioi 0) := by
      exact Real.logb_injOn_pos (by norm_num)

    rcases this with h3 | h3
    · have h3 : a=1 := by linarith
      unfold a at h3

      have : Real.logb 5 5 = 1 := by exact Real.logb_self_eq_one (by norm_num)
      rw [← this] at h3

      have : Real.logb 5 (x + 4) = Real.logb 5 5 ↔ x+4=5 := by
        apply hlog_inj.eq_iff
        all_goals
          refine Set.mem_Ioi.mpr ?_
          linarith
      rw [this] at h3

      have : x=1 := by linarith
      linarith
    · have h3 : b=2 := by linarith
      unfold b at h3

      have : Real.logb 5 25 = 2 := by
        refine (Real.logb_eq_iff_rpow_eq ?_ ?_ ?_).mpr ?_
        repeat norm_num
      rw [← this] at h3

      have : Real.logb 5 (x - 1) = Real.logb 5 25 ↔ x-1=25 := by
        apply hlog_inj.eq_iff
        all_goals
          refine Set.mem_Ioi.mpr ?_
          linarith
      rw [this] at h3

      linarith

    nlinarith
    linarith
  · intro h
    rw [h]
    norm_num
    have h2 : (30 : ℝ) ≠ 0 := by norm_num
    have h3 : (25 : ℝ) ≠ 0 := by norm_num

    have : Real.logb 5 25 = 2 := by
      refine (Real.logb_eq_iff_rpow_eq ?_ ?_ ?_).mpr ?_
      repeat norm_num
    rw [← this]
    rw [← Real.logb_div]

    have : Real.logb 5 25 = (2 : ℕ) := by
      norm_num
      exact this
    rw [this, mul_comm, ← Real.logb_pow]

    repeat norm_num
