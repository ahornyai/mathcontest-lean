import Mathlib.Tactic
/-
OKTV 2011/2012, II. kategória, I. forduló, 1. feladat:

Oldjuk meg a valós számok halmazán a következő egyenletet:
(2*x^2 - x - 3)^4 + (2*x^2 - x - 3)^2 * (2*x^2 + x - 6)^2 + (2*x^2 + x - 6)^4 = 0
----
bizonyítsuk be, hogy az egyetlen megoldás az 1.5
-/
theorem oktv2011_ii_i_i (x : ℝ) : (2*x^2 - x - 3)^4 + (2*x^2 - x - 3)^2 * (2*x^2 + x - 6)^2 + (2*x^2 + x - 6)^4 = 0 ↔ x=1.5 := by
  constructor
  · intro h
    have : (2*x^2 - x - 3)^4 + (2*x^2 - x - 3)^2 * (2*x^2 + x - 6)^2 + (2*x^2 + x - 6)^4 = (2*x^2 - x - 3)^4 + ((2*x^2 - x - 3)*(2*x^2 + x - 6))^2 + (2*x^2 + x - 6)^4 := by ring_nf
    rw [this] at h

    have h1term_nonneg : (2*x^2 - x - 3)^4 ≥ 0 := by
      refine Even.pow_nonneg ?_ (2 * x ^ 2 - x - 3)
      exact Nat.even_iff.mpr rfl

    have h2term_nonneg : ((2*x^2 - x - 3)*(2*x^2 + x - 6))^2 ≥ 0 := by exact sq_nonneg ((2 * x ^ 2 - x - 3) * (2 * x ^ 2 + x - 6))

    have h3term_nonneg : (2*x^2 + x - 6)^4 ≥ 0 := by
      refine Even.pow_nonneg ?_ (2 * x ^ 2 + x - 6)
      exact Nat.even_iff.mpr rfl

    have : (2*x^2 - x - 3)^4 = 0 := by linarith
    have : 2*x^2 - x - 3 = 0 := by exact pow_eq_zero this
    have : (x-1.5)*(x+1) = 0:= by linarith
    have : x-1.5=0 ∨ x+1=0 := by exact mul_eq_zero.mp this

    rcases this with h1 | h1
    · linarith
    · have : x=-1 := by linarith
      rw [this] at h
      norm_num at h
  · intro h
    rw [h]
    norm_num
