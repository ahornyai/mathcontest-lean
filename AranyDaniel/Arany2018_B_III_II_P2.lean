import Mathlib.Tactic

/-
Arany Dániel 2018/2019 Kezdők III. kategória II. forduló II. feladat

Mely f : ℤ → ℤ függvényekre igaz, hogy tetszőleges x, y egész számokra
f (x + f(y)) = f(x) + y
----------------------
Bizonyítsuk, hogy kizárólag az f(x) = x valamint f(x) = -x a megoldás.
-/
def SolutionSet : Set (ℤ → ℤ) := { f | (∀ x, f x = x) ∨ (∀ x, f x = -x) }

theorem arany2018_beginners_iii_ii_ii {f : ℤ → ℤ} : f ∈ SolutionSet ↔ ∀ x y, f (x + f y) = f x + y := by
  constructor
  · intro h x y

    rcases h with h | h <;> simp_all
    ring
  · intro h

    have h₁ : Function.Injective f := by
      unfold Function.Injective
      intro x y hf

      have h₂ : f (x + f x) = f x + x := by exact h x x
      have h₃ : f (x + f y) = f x + y := by exact h x y

      rw [← hf] at h₃

      linarith

    have hf_0_eq_0 : f 0 = 0 := by
      specialize h 0 0
      norm_num at h
      exact h₁ (h₁ (congrArg f h))

    have h₂ : Function.Involutive f := by
      unfold Function.Involutive
      intro x

      specialize h 0 x
      norm_num at h

      rw [h, hf_0_eq_0]
      norm_num

    have h₃ : ∀ x y, f x + f y = f (x + y) := by
      intro x y
      specialize h (f x) y

      rw [h₂] at h
      rw [show (x + y = f (f (x + y))) by rw [h₂]] at h
      rw [h₁ h]

    have h₄ : ∀ x, f x = f 1 * x := by
      intro x

      induction x with
      | zero => simp_all
      | succ n ih => 
        specialize h₃ n 1

        rw [← h₃]
        linarith
      | pred n ih => grind

    have h₅ : f 1 = 1 ∨ f 1 = -1 := by
      have : (f 1)^2 - 1^2 = 0 := by grind
      rw [sq_sub_sq] at this
      simp at this

      rcases this with h₆ | h₆
      · right
        linarith
      · left
        linarith

    rcases h₅ with h₆ | h₆
    · left
      intro x
      specialize h₄ x

      rw [h₆, one_mul] at h₄

      exact h₄
    · right
      intro x
      specialize h₄ x

      rw [h₆, Int.neg_one_mul] at h₄

      exact h₄
