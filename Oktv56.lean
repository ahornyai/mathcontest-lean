import Mathlib.Tactic

/-
OKTV 2024/2025, IiI. kategória, I. forduló, 3. feladat:

Az a(n) sorozatot a következő rekurzióval értelmezzük: a 1 = 1, és n > 0 esetén a(n+1) = a(n)^2 + 3*a(n) + 1
Mutassuk meg, hogy 1/(2+a(1)) + 1/(2+a(2)) + ... + 1/(2+a(2024)) < 1/2
----------------
Megjegyzés: Az egyszerűbb bizonyítás kedvéért újraindexeltem a sorozatot úgy, hogy a 0 = 1 legyen.
-/
theorem oktv2024_iii_iii {a : ℕ → ℕ} (ha_0 : a 0 = 1) (ha : ∀ n, a (n+1) = (a n)^2 + 3 * a n + 1) : ∑ x ∈ Finset.range 2024, (1/(2+a x) : ℚ) < 1/2 := by
  have ha_1 : a 1 = 5 := by
    specialize ha 0
    rw [zero_add, ha_0] at ha
    rw [ha]
    norm_num

  have h₁ : ∀ n, ∑ x ∈ Finset.range n, (1/(2+a x) : ℚ) = 1/2 - 1/(1 + a (n)) := by  
    intro n

    induction n with
    | zero => simp; rw [ha_0]; norm_num
    | succ n ih => 
      rw [Finset.sum_range_succ, ih, ha]
      field_simp
      ring

  rw [h₁]
  norm_num
  linarith
