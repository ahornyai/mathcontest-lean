import Mathlib.Tactic

/-
Arany Dániel 2015/16 Kezdők II. kategória, III. forduló I. feladat

Melyek azok a pozitív természetes számok, amelyek reciprokának tizedes tört alakja véges, és a szám köbének 7-szer annyi osztója van, mint magának a számnak?
-----
akkor lesz egy szám tizedes tört alakja véges, ha kizárólag 2 és 5 prímtényezői vannak
bizonyítsuk, hogy a két lehetséges megoldás n=64000, n=15625000
-/
lemma eq_of_mul_eq_prime {x y p : ℕ} (hp : Nat.Prime p) (h : x * y = p) : x = 1 ∧ y = p ∨ x = p ∧ y = 1 := by
  have : p ∣ x ∨ p ∣ y := by
    refine (Nat.Prime.dvd_mul hp).mp ?_
    exact dvd_of_eq (id (Eq.symm h))

  rcases this with h1 | h1
  · obtain ⟨k, hk⟩ := h1
    rw [hk] at h

    have : p*(k*y) = p*1 := by linarith
    rw [Nat.mul_right_inj (by exact Nat.Prime.ne_zero hp)] at this

    have : k=1 ∧ y=1 := by exact mul_eq_one.mp this
    obtain ⟨hk_eq, hy_eq⟩ := this

    rw [hk_eq] at hk

    omega
  · obtain ⟨k, hk⟩ := h1
    rw [hk] at h

    have : p*(k*x) = p*1 := by linarith
    rw [Nat.mul_right_inj (by exact Nat.Prime.ne_zero hp)] at this

    have : k=1 ∧ x=1 := by exact mul_eq_one.mp this
    obtain ⟨hk_eq, hy_eq⟩ := this

    rw [hk_eq] at hk

    omega

theorem arany2015_beginner_ii_iii_i (n : ℕ) (hn_neq_0 : n ≠ 0)
  : (n.primeFactors = {2, 5} ∧ 7 * n.divisors.card = (n^3).divisors.card) ↔ n=64000 ∨ n=15625000 := by
  constructor
  · intro h
    obtain ⟨h1, h2⟩ := h

    have : (n^3).primeFactors = {2, 5} := by
      rw [Nat.primeFactors_pow]
      exact h1
      decide

    repeat rw [Nat.card_divisors] at h2
    rw [h1, this] at h2
    norm_num at h2

    have hn_facts : n = ∏ p1 ∈ n.primeFactors, p1 ^ n.factorization p1 := by
      rw [← Nat.factorization_prod_pow_eq_self hn_neq_0]
      congr
      exact Eq.symm (Nat.factorization_prod_pow_eq_self hn_neq_0)
    rw [h1] at hn_facts
    norm_num at hn_facts

    let a := n.factorization 2
    let b := n.factorization 5

    have : a ≥ 2 := by nlinarith
    have : b ≥ 2 := by nlinarith

    have : ((a-2)*(b-2) : ℤ) = 7 := by linarith
    norm_cast at this

    rcases eq_of_mul_eq_prime (by decide) this with h3 | h3
    · have ha_eq : a=3 := by omega
      have hb_eq : b=9 := by omega

      unfold a at ha_eq
      unfold b at hb_eq

      rw [ha_eq, hb_eq] at hn_facts

      omega
    · have ha_eq : a=9 := by omega
      have hb_eq : b=3 := by omega

      unfold a at ha_eq
      unfold b at hb_eq

      rw [ha_eq, hb_eq] at hn_facts

      omega

    exact pow_ne_zero 3 hn_neq_0
    exact hn_neq_0
  · intro h
    rcases h with rfl | rfl
    · have : 64000 = 2^9*5^3 := by norm_num
      repeat rw [this]

      have h1 : (2^9*5^3).primeFactors = {2, 5} := by
        rw [Nat.primeFactors_mul]
        repeat rw [Nat.primeFactors_prime_pow]
        rfl
        all_goals norm_num
      rw [h1]

      constructor
      · rfl
      · repeat rw [Nat.card_divisors]
        rw [h1, Nat.primeFactors_pow, h1]

        norm_num
        rw [this]

        have : 262144000000000 = 2^27*5^9 := by norm_num
        rw [this]

        repeat rw [Nat.factorization_mul]
        repeat rw [Nat.factorization_pow]
        all_goals norm_num
    · have : 15625000 = 2^3*5^9 := by norm_num
      repeat rw [this]

      have h1 : (2^3*5^9).primeFactors = {2, 5} := by
        rw [Nat.primeFactors_mul]
        repeat rw [Nat.primeFactors_prime_pow]
        rfl
        all_goals norm_num
      rw [h1]

      constructor
      · rfl
      · repeat rw [Nat.card_divisors]
        rw [h1, Nat.primeFactors_pow, h1]

        norm_num
        rw [this]

        have : 3814697265625000000000 = 2^9*5^27 := by norm_num
        rw [this]

        repeat rw [Nat.factorization_mul]
        repeat rw [Nat.factorization_pow]
        all_goals norm_num
