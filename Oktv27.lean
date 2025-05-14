import Mathlib.Tactic
/-
OKTV 2019/2020, III. kategória, I. forduló, 1. feladat:

Jelölje d(n) az n > 0 egész szám pozitív osztóinak a számát. Tegyük
fel, hogy d(k)^2 = d(k^4). Bizonyítsuk be, hogy alkalmas j ≥ 0 egészre
d(k) = 3^j
-/
theorem oktv_2004_iii_i (k : ℕ) (hk_pos : k > 0)
  (h : k.divisors.card ^ 2 = (k^4).divisors.card) : ∃j, k.divisors.card = 3^j := by
  repeat rw [Nat.card_divisors] at h

  rw [Nat.primeFactors_pow] at h
  rw [← Finset.prod_pow] at h
  rw [Nat.factorization_pow] at h

  have : ∏ x ∈ k.primeFactors, (k.factorization x + 1) ^ 2 = ∏ x ∈ k.primeFactors, ((k.factorization x)^2 + 2*k.factorization x + 1) := by
    rw [Finset.prod_congr]
    exact rfl
    intro x h
    linarith
  rw [this] at h

  have : ∏ x ∈ k.primeFactors, (k.factorization x ^ 2 + 2 * k.factorization x + 1) = ∏ x ∈ k.primeFactors, ((k^4).factorization x + 1) ↔ ∀ x ∈ k.primeFactors, (k.factorization x ^ 2 + 2 * k.factorization x + 1) = ((k^4).factorization) x + 1 := by
    constructor
    · intro h1 x hx
      --rw [Finset.prod_congr] at h1

      sorry
    · sorry


  sorry

  norm_num
  refine pow_ne_zero 4 ?_
  exact Nat.not_eq_zero_of_lt hk_pos
  exact Nat.not_eq_zero_of_lt hk_pos
