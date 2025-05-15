import Mathlib.Tactic
/-
OKTV 2011/2012, I. kategória, I. forduló, 1. feladat:

Oldja meg a valós számok halmazán az (x-3)^4 + (x-5)^4 = 82 egyenletet!
--------------------------------
Bizonyítsuk be, hogy a kizárólagos megoldások x=2 és x=6
-/
theorem oktv_2011_i_i (x : ℝ) : (x-3)^4 + (x-5)^4 = 82 ↔ (x=2 ∨ x=6) := by
  constructor
  · intro h
    let a := x-4
    let y := a^2

    have : a^4 + 6*a^2 + 1 = 41 := by
      unfold a
      linarith

    have : y^2 + 6*y - 40 = 0 := by
      unfold y
      linarith
    have : (y-4)*(y+10) = 0 := by linarith
    norm_num at this

    rcases this with h1 | h1
    · unfold y a at h1

      have : (4 : ℝ) = 2^2 := by norm_num
      nth_rewrite 2 [this] at h1
      rw [sq_sub_sq] at h1
      norm_num at h1

      rcases h1 with h2 | h2
      · have : x=2 := by linarith

        left
        exact this
      · have : x=6 := by linarith

        right
        exact this
    · unfold y at h1
      nlinarith
  · intro h
    rcases h with rfl | rfl
    all_goals norm_num
