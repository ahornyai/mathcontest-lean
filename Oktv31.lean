import Mathlib.Tactic
/-
innen valamelyiket:
https://www.oktatas.hu/pub_bin/dload/kozoktatas/tanulmanyi_versenyek/oktv/oktv_2008_2009/mat2_javut2f_oktv0809.pdf

-/
noncomputable def f (x : ℝ) : ℝ := ((Real.sqrt 11)/5)^x + ((Real.sqrt 14)/5)^x

theorem oktv_2009_ii_iii (x : ℝ) : 11^x + 14^x = 25^x - 2*(Real.sqrt 154)^x ↔ x=2 := by
  sorry
