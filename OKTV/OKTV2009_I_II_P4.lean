import Mathlib.Tactic
/-
OKTV 2009/2010, I. kategória, II. forduló, 4. feladat:

Oldja meg az
|x-4*y+1| + |y-3*x-2| + |x+y+2| + |x+2*y+3| = 4
egyenletet, ha x ∈ ℤ és y ∈ ℤ
--------------------------------
Bizonyítsuk be, hogy az összes megoldás: (x, y) = {(-1, 0), (-1, -1)}
-/
def SolutionSet : Set (ℤ × ℤ) := {(-1, 0), (-1, -1)}

theorem oktv2009_i_ii_iv (x y : ℤ) : |x-4*y+1| + |y-3*x-2| + |x+y+2| + |x+2*y+3| = 4 ↔ ⟨x,y⟩ ∈ SolutionSet := by
  unfold SolutionSet
  constructor
  · intro h

    have h1 : |x-4*y+1| + |y-3*x-2| + |x+y+2| + |x+2*y+3| ≥ x-4*y+1 + y-3*x-2 + x+y+2 + x+2*y+3 := by
      rw [h]
      linarith

    /-
    have : |x-4*y+1| ≥ x-4*y+1 := by exact le_abs_self (x - 4 * y + 1)
    have : |y-3*x-2| ≥ y-3*x-2 := by exact le_abs_self (y - 3 * x - 2)
    have : |x+y+2| ≥ x+y+2 := by exact le_abs_self (x + y + 2)
    have : |x+2*y+3| ≥ x+2*y+3 := by exact le_abs_self (x + 2 * y + 3)
    -/

    sorry
  · intro h
    simp at h

    rcases h with h1 | h1
    all_goals
      obtain ⟨rfl, rfl⟩ := h1
      norm_num

example {x : ℤ} : |x| ≥ x := by
  exact le_abs_self x
