import Mathlib.Tactic

/-
OKTV 2014/2015, II. kategória, I. forduló, 3. feladat:

Legyen a(1) = 1, a sorozat további elemeit a következő összefüggés határozza meg:
a(n+1) * a(n) = 4*(a(n+1) − 1)
Igazoljuk, hogy a sorozat első 2025 darab tagjának szorzata nagyobb, mint 2^2014
----
Megjegyzés: Az egyszerűbb bizonyítás érdekében újraindexeltem a feladatot úgy, hogy a(0)=1 legyen.
-/
theorem oktv2014_ii_i_iii {a : ℕ → ℚ} (ha_0 : a 0 = 1) (h : ∀ n, a (n+1) * a n = 4 * (a (n+1) - 1))
  : ∏ x ∈ Finset.range 2025, a x ≥ 2^2014 := by
  have ha : ∀ n, a n = (2*n+2)/(n+2) := by
    intro n

    induction n with
    | zero => rw [ha_0]; simp
    | succ n ih =>
      specialize h n
      rw [ih] at h
      field_simp
      field_simp at h
      linarith

  have : ∀ n, ∏ x ∈ Finset.range n, a x = 2^n/(n+1) := by
    intro n

    induction n with
    | zero => simp
    | succ n ih =>
      rw [Finset.prod_range_succ, ih, ha]
      field_simp
      ring

  rw [this]
  norm_num
