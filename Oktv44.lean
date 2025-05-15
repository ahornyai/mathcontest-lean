import Mathlib.Tactic
/-
OKTV 2018/2019, I. kategória, III. forduló, 1. feladat:

Határozza meg az a; b; c; d; pozitív prímszámokat, ha tudjuk, hogy a
log a + log b + log c + log d és a 2*a^b + c^d kifejezések értéke
(nem feltétlenül azonos) pozitív prímszám
--------------------------------
az egyszerűség kedvéért logaritmus azonosságok használatával írom fel a problémát
todo: megcsinálni 0-ról
bizonyítsuk be, hogy az egyetlen megoldás az (a,b,c,d)=(2, 5, 5, 2)
-/
theorem oktv_2018_i_i (a b c d p q : ℕ) (ha : Nat.Prime a) (hb : Nat.Prime b) (hc : Nat.Prime c) (hd : Nat.Prime d)
  (hp : p = Nat.log 10 (a*b*c*d)) (hq : q = 2*a^b + c^d)
  : (Nat.Prime p ∧ Nat.Prime q) ↔ a=2 ∧ b=5 ∧ c=5 ∧ d=2 := by
  constructor
  · intro h
    obtain ⟨h1, h2⟩ := h
    have : 10^p = a*b*c*d := by
      rw [hp]
      sorry
    sorry
  · intro h
    obtain ⟨rfl, rfl, rfl, rfl⟩ := h
    norm_num
