import Mathlib.Tactic
/-
OKTV 2020/2021, I. kategória, II. forduló, 1. feladat:

Melyek azok az x, y valós számpárok, amelyekre teljesül az alábbi egyenletrendszer?
(x+y)*(x^2-y^2) = 400
(x-y)*(x^2+y^2) = 232
--------------------------------
igazoljuk, hogy az egyenletrendszer megoldásai: (x,y) ∈ {(7, 3), (-3, -7)}
-/
def SolutionSet : Set (ℝ × ℝ) := {(7, 3), (-3, -7)}

theorem oktv2020_i_ii_i (x y : ℝ) : ((x+y)*(x^2-y^2) = 400 ∧ (x-y)*(x^2+y^2) = 232) ↔ ⟨x, y⟩ ∈ SolutionSet := by
  unfold SolutionSet
  constructor
  · intro h
    obtain ⟨h1, h2⟩ := h

    have h3 : x*y*(x-y)=84 := by nlinarith
    have h4 : (x-y)^3=4^3 := by nlinarith
    rw [pow_left_inj₀ (by nlinarith) (by norm_num) (by norm_num)] at h4

    have hy_eq : y = x - 4 := by linarith
    rw [h4, hy_eq] at h3

    have : (x+3)*(x-7) = 0 := by linarith
    have : x+3=0 ∨ x-7=0 := by exact mul_eq_zero.mp this

    rcases this with h1 | h1
    · have : x=-3 := by linarith
      rw [this] at hy_eq
      rw [hy_eq, this]
      norm_num
    · have : x=7 := by linarith
      rw [this] at hy_eq
      rw [hy_eq, this]
      norm_num
  · intro h
    simp at h

    rcases h with h1 | h1
    all_goals
      obtain ⟨rfl, rfl⟩ := h1
      norm_num
