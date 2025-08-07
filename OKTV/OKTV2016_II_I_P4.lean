import Mathlib.Tactic
/-
OKTV 2016/2017, II. kategória, I. forduló, 4. feladat:

Oldjuk meg a következő egyenletet az egész számok halmazán:
x*(x + 2) = y^2*(y^2 + 1)
-/
def SolutionSet : Set (ℤ × ℤ) := {(0, 0), (-2, 0)}

theorem oktv2016_ii_i_iv (x y : ℤ) : ⟨x, y⟩ ∈ SolutionSet ↔ x*(x + 2) = y^2*(y^2 + 1) := by
  unfold SolutionSet
  constructor
  · intro h
    simp at h

    rcases h with h | h
    all_goals
      obtain ⟨rfl, rfl⟩ := h
      rfl
  · intro h
    refine Set.mem_insert_iff.mpr ?_

    have hxp1_gt_y_sq_sq: (y^2)^2 < (x+1)^2 := by nlinarith
    have hxp1_leq_y_sqp1_sq: (x+1)^2 ≤ (y^2+1)^2 := by nlinarith

    rw [sq_lt_sq, abs_sq y] at hxp1_gt_y_sq_sq

    have : (x+1)^2 = (y^2+1)^2 := by
      by_contra!

      have hyp1_nonneg: |y^2+1| = y^2+1 := by exact abs_of_nonneg (by linarith)
      have : (x+1)^2 < (y^2+1)^2 := by omega

      rw [sq_lt_sq, hyp1_nonneg] at this

      omega

    rw [sq_eq_sq_iff_eq_or_eq_neg] at this

    rcases this with h1 | h1
    · have : y=0 := by nlinarith
      rw [this] at h1
      norm_num at h1

      refine Or.symm (Or.inr ?_)
      exact Prod.ext h1 this
    · have y_val : y = 0 := by nlinarith
      rw [y_val] at h1

      have x_val : x =-2 := by  exact (Int.add_left_inj 1).mp h1

      refine Or.symm (Or.inl ?_)
      exact Prod.ext x_val y_val
