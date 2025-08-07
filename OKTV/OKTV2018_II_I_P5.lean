import Mathlib.Tactic
/-
OKTV 2018/2019, II. kategória, I. forduló, 5. feladat:

Mi lehet az a pozitív egész szám, amelynek összesen 10 pozitív osztója van, ebbe
beleszámoltuk az 1-et és magát a számot is, és ennek a tíz számnak az összege 34364?
----------
Bizonyítsuk, hogy a megoldás 22923 vagy 26875
-/
theorem oktv2018_ii_i_v (x : ℕ) (hxpos : x > 0) : ((Nat.divisors x).card = 10 ∧ (∑ d ∈ Nat.divisors x, d) = 34364) ↔ x=22923 ∨ x=26875 := by
  constructor
  · intro h
    obtain ⟨h1, h2⟩ := h

    rw [Nat.card_divisors] at h1

    have h10_divs : Nat.divisors 10 = {1, 2, 5, 10} := by decide +kernel

    have h_primefac_div_10 : ∀ x_1 ∈ x.primeFactors, (x.factorization x_1 + 1) ∣ 10 := by
      rw [← h1]
      exact fun x_1 a ↦ Finset.dvd_prod_of_mem (fun i ↦ x.factorization i + 1) a

    have h_primefac_in_10_div: ∀ x_1 ∈ x.primeFactors, (x.factorization x_1 + 1) ∈ ({1,2,5,10} : Finset ℕ) := by
      rw [← h10_divs]
      refine fun x_1 a ↦ ?_
      refine Nat.mem_divisors.mpr ?_

      constructor
      · exact h_primefac_div_10 x_1 a
      · norm_num



    sorry
    exact Nat.not_eq_zero_of_lt hxpos
  · intro h
    rcases h with h | h
    · rw [h]
      have : 22923 = 3^4*283^1 := by rfl
      rw [this]

      have h_primes : (3^4*283^1).primeFactors = {3, 283} := by
        rw [Nat.primeFactors_mul]
        repeat rw [Nat.primeFactors_prime_pow]
        all_goals norm_num
        rfl

      constructor
      · rw [Nat.card_divisors, h_primes, Nat.factorization_mul]
        repeat rw [Nat.factorization_pow]
        all_goals norm_num
      · rw [Nat.sum_divisors, h_primes, Nat.factorization_mul]
        repeat rw [Nat.factorization_pow]
        all_goals norm_num
    · rw [h]
      have : 26875 = 5^4*43^1 := by rfl
      rw [this]

      have h_primes : (5^4*43^1).primeFactors = {5, 43} := by
        rw [Nat.primeFactors_mul]
        repeat rw [Nat.primeFactors_prime_pow]
        all_goals norm_num
        rfl

      constructor
      · rw [Nat.card_divisors, h_primes, Nat.factorization_mul]
        repeat rw [Nat.factorization_pow]
        all_goals norm_num
      · rw [Nat.sum_divisors, h_primes, Nat.factorization_mul]
        repeat rw [Nat.factorization_pow]
        all_goals norm_num
