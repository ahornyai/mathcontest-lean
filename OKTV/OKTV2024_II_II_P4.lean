import Mathlib.Tactic

/-
OKTV 2024/2025, II. kategória, II. forduló, 4. feladat:

Legyen az f függvény értelmezési tartománya a valós számok halmaza. Keressük
meg az összes olyan f függvényt, amelyre minden valós x-re f (x) valós szám, továbbá teljesül az alábbi egyenlet:
f^2(4 − x) + 4*f^2(x + 4) − 9 = 2*(f(4 − x) + 3)*(2*f(x + 4) − 3)
----------------
Bizonyítsuk, hogy az egyetlen ilyen függvény az f: ℝ → ℝ, f(x) = 3
-/
def SolutionSet : (Set (ℝ → ℝ)) := {f | ∀ x, f x = 3}

theorem oktv2024_ii_ii_iv {f : ℝ → ℝ} : f ∈ SolutionSet ↔ ∀ x, (f (4-x))^2 + 4*(f (x+4))^2 - 9 = 2 * (f (4-x) + 3) * (2 * f (x+4) - 3) := by
  constructor
  · intro h x
    repeat rw [h]
    norm_num
  · intro h

    have h₁ : ∀ x, f (4-x) - 2 * f (x+4) + 3 = 0 := by
      intro x
      specialize h x
      nlinarith

    have h₂ : ∀ x, f (x+4) - 2 * f (4-x) + 3 = 0 := by
      intro x
      specialize h₁ (-x)

      rw [show (4 - -x = x+4) by ring] at h₁
      rw [show (-x + 4 = 4-x) by ring] at h₁

      exact h₁

    have h₃ : ∀ x, -3 * f (x+4) + 9 = 0 := by
      intro x
      specialize h₁ x
      specialize h₂ x
      linarith

    intro x
    specialize h₃ (x-4)

    rw [sub_add_cancel] at h₃
    linarith
