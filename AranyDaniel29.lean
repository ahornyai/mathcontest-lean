import Mathlib.Tactic

/-
Arany Dániel 2012/2013 Kezdők II. kategória III. forduló III. feladat

Melyek azok az n pozitív egész számok, amelyeknek prímtényezős felbontásában csak
a 2 és a 3 hatványai szerepelnek, és n összes osztójának a száma harmadrésze n^2 osztói
számának?
-----------------------------------
Bizonyítsuk, hogy n = 144 vagy n = 324
-/
theorem eq_of_mul_eq_three {x y : ℕ} (h : x * y = 3) :
    x = 1 ∧ y = 3 ∨ x = 3 ∧ y = 1 := by
  have h₁ : (x, y) ∈ Nat.divisorsAntidiagonal 3 := by simpa using h
  have h₂ : Nat.divisorsAntidiagonal 3 = {(1, 3), (3, 1)} := by rfl
  simpa [h₂] using h₁

theorem arany2013_beginner_ii_iii_iii (n : ℕ) (hn_neq_0 : n ≠ 0)
  : (n.primeFactors = {2, 3}) ∧ (3*n.divisors.card = (n^2).divisors.card) ↔ n=144 ∨ n=324 := by
  constructor
  · intro h
    obtain ⟨h1, h2⟩ := h
    
    repeat rw [Nat.card_divisors] at h2
    
    have : (n^2).primeFactors = {2, 3} := by
      rw [Nat.primeFactors_pow]
      exact h1
      decide
    
    rw [h1, this] at h2
    norm_num at h2

    have hn_facts : n = ∏ p1 ∈ n.primeFactors, p1 ^ n.factorization p1 := by
      rw [← Nat.factorization_prod_pow_eq_self hn_neq_0]
      congr
      exact Eq.symm (Nat.factorization_prod_pow_eq_self hn_neq_0)
    rw [h1] at hn_facts
    norm_num at hn_facts

    let p := n.factorization 2
    let q := n.factorization 3

    by_cases h3 : p > 2
    · by_cases h4 : q > 2
      · have : (2*p+1)*(2*q+1) = 3*(p+1)*(q+1) := by linarith
        
        have h5 : (2*p+1)*(2*q+1) - 3*(p+1)*(q+1) = 0 := by omega

        have : (2*p+1)*(2*q+1) = 4*p*q + 2*p + 2*q + 1 := by ring
        rw [this] at h5

        have : 3*(p+1)*(q+1) = 3*p*q + 3*p + 3*q + 3 := by ring
        rw [this] at h5

        have : 4 * p * q + 2 * p + 2 * q + 1 - (3 * p * q + 3 * p + 3 * q + 3) = p*q - p - q - 2 := by nlinarith
        rw [this] at h5
        
        have : p * q - p - q - 2 = (p-1)*(q-1) - 3 := by nlinarith
        rw [this] at h5

        have : (p - 1) * (q - 1) ≥ 3 := by nlinarith
        have : (p - 1) * (q - 1) = 3 := by omega
        
        rcases eq_of_mul_eq_three this with h6 | h6
        · have hp : p=2 := by omega
          have hq : q=4 := by omega 
          
          unfold p at hp
          unfold q at hq

          rw [hp, hq] at hn_facts

          omega
        · have hp : p=4 := by omega
          have hq : q=2 := by omega

          unfold p at hp
          unfold q at hq

          rw [hp, hq] at hn_facts

          omega
      · interval_cases hq: q
        · unfold q at hq
          rw [hq] at h2
          omega
        · unfold q at hq
          rw [hq] at h2
          omega
        · unfold q at hq
          rw [hq] at h2

          have : n.factorization 2 = 4 := by omega
          rw [this, hq] at hn_facts
          
          omega
    · interval_cases hp: p
      · unfold p at hp
        rw [hp] at h2
        omega
      · unfold p at hp
        rw [hp] at h2
        omega
      · unfold p at hp
        rw [hp] at h2
        
        have : n.factorization 3 = 4 := by omega
        rw [this, hp] at hn_facts
        
        omega
    
    by_contra!
    rw [sq_eq_zero_iff] at this
    contradiction
    exact hn_neq_0
  · intro h
    rcases h with rfl | rfl
    · have : 144 = 2^4 * 3^2 := by decide
      rw [this]

      have h_sq : 20736 = 2^8 * 3^4 := by decide

      have primefacs : (2^4 * 3^2).primeFactors = {2, 3} := by
        rw [Nat.primeFactors_mul]
        repeat rw [Nat.primeFactors_prime_pow]
        all_goals trivial
      
      constructor
      · exact primefacs
      · repeat rw [Nat.card_divisors]
        
        rw [Nat.primeFactors_pow]
        repeat rw [primefacs]

        norm_num
        rw [this, h_sq]
        repeat rw [Nat.factorization_mul]
        repeat rw [Nat.factorization_pow]
        
        all_goals norm_num
    · have : 324 = 2^2 * 3^4 := by decide
      rw [this]

      have h_sq : 104976 = 2^4 * 3^8 := by decide

      have primefacs : (2^2 * 3^4).primeFactors = {2, 3} := by
        rw [Nat.primeFactors_mul]
        repeat rw [Nat.primeFactors_prime_pow]
        all_goals trivial
      
      constructor
      · exact primefacs
      · repeat rw [Nat.card_divisors]
        
        rw [Nat.primeFactors_pow]
        repeat rw [primefacs]

        norm_num
        rw [this, h_sq]
        repeat rw [Nat.factorization_mul]
        repeat rw [Nat.factorization_pow]
        
        all_goals norm_num
