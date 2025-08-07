import Mathlib.Tactic

/-
OKTV 2020/2021, I. kategória, II. forduló, 2. feladat:

Legyen f(x) a természetes számok halmazán értelmezett olyan függvény, amely eleget tesz az f(x) + f(f(x)) = 12*x + 40  egyenletnek, és f(21) = 71.
Feltéve, hogy a megadott tulajdonságokkal rendelkező függvény létezik, van-e olyan szám, amelyre f(x) = 2021
----
Bizonyítsuk, hogy létezik ilyen függvény, a grind tactic automatikusan megoldja
-/
theorem oktv_i_ii_ii {f : ℕ → ℕ}
  (h₁ : ∀x, f x + f (f x) = 12*x + 40) (h₂ : f 21 = 71) : ∃ x, f x = 2021 := by
  grind
