import Mathlib.Tactic

theorem eq_of_mul_eq_prime {x y p : ℕ} (hp : Nat.Prime p) (h : x * y = p) : x = 1 ∧ y = p ∨ x = p ∧ y = 1 := by
  have h₁ : x ∣ p := by exact Dvd.intro y h
  have h₂ : x = 1 ∨ x=p := by
    rw [Nat.dvd_prime hp] at h₁
    exact h₁
  
  rcases h₂ with h₃ | h₃
  · rw [h₃, one_mul] at h

    left
    exact ⟨h₃, h⟩
  · have h₄ : y = 1 := by
      rw [h₃] at h

      have : p*(y-1) = 0 := by
        rw [Nat.mul_sub_left_distrib, mul_one]
        exact Eq.symm (Nat.eq_sub_of_add_eq' (id (Eq.symm h)))

      simp at this
      rcases this with h₅ | h₅
      · rw [h₅] at hp
        contradiction
      · have : y ≠ 0 := by
          by_contra!
          rw [this, mul_zero] at h
          rw [← h] at hp
          contradiction
        
        omega
    
    right
    exact ⟨h₃, h₄⟩

/-
Arany Dániel 2012/2013 I. kategória I. forduló III. feladat

Melyek azok az N pozitív egész számok, amelyeknek prímtényezős felbontásában csak
a 2 és a 3 hatványai szerepelnek, és N összes osztójának a száma harmadrésze N 2 osztói
számának?
----------------------
Bizonyítsuk, hogy a megoldáshalmaz: n ∈ {144, 324}
-/
theorem arany2013_advanced_i_i_iii {n : ℕ} (hn : n.primeFactors = {2, 3}) : 3*n.divisors.card = (n^2).divisors.card ↔ n=144 ∨ n=324 := by
  have hn_neq_0 : n ≠ 0 := by
    by_contra!
    rw [this, Nat.primeFactors_zero] at hn
    contradiction

  constructor
  · intro h

    have hn_neq_0 : n ≠ 0 := by
      by_contra!
      rw [this, Nat.primeFactors_zero] at hn
      contradiction
    
    repeat rw [Nat.card_divisors] at h
    rw [Nat.primeFactors_pow, hn] at h
    simp at h

    let p : ℤ := n.factorization 2
    let q : ℤ := n.factorization 3

    have h₁ : (p-1)*(q-1) = 3 := by linarith
    unfold p q at h₁
    
    have h₂ : n.factorization 2 ≥ 1 := by
      refine (Nat.Prime.dvd_iff_one_le_factorization ?_ hn_neq_0).mp ?_
      exact Nat.prime_two
      refine Nat.dvd_of_mem_primeFactors ?_
      rw [hn]
      exact Finset.mem_insert_self 2 {3}
    
    have h₃ : n.factorization 3 ≥ 1 := by
      refine (Nat.Prime.dvd_iff_one_le_factorization ?_ hn_neq_0).mp ?_
      exact Nat.prime_three
      refine Nat.dvd_of_mem_primeFactors ?_
      rw [hn]
      simp

    norm_cast at h₁

    apply eq_of_mul_eq_prime at h₁
    
    rcases h₁ with h₄ | h₄
    · obtain ⟨h₄, h₅⟩ := h₄
      
      have h₄ : n.factorization 2 = 2 := by omega 
      have h₅ : n.factorization 3 = 4 := by omega

      rw [h₄, h₅] at h
      right

      rw [← Nat.factorization_prod_pow_eq_self hn_neq_0]
      rw [Nat.prod_factorization_eq_prod_primeFactors]
      rw [hn]
      
      simp
      rw [h₄, h₅]
      norm_num
    · obtain ⟨h₄, h₅⟩ := h₄
      
      have h₄ : n.factorization 2 = 4 := by omega 
      have h₅ : n.factorization 3 = 2 := by omega

      rw [h₄, h₅] at h
      left

      rw [← Nat.factorization_prod_pow_eq_self hn_neq_0]
      rw [Nat.prod_factorization_eq_prod_primeFactors]
      rw [hn]
      
      simp
      rw [h₄, h₅]
      norm_num
    
    exact Nat.prime_three
    decide
    exact pow_ne_zero 2 hn_neq_0
    exact hn_neq_0
  · intro h

    repeat rw [Nat.card_divisors]
    rw [Nat.primeFactors_pow, hn]
    simp

    rcases h with rfl | rfl
    · have : 144 = 2^4 * 3^2 := by norm_num
      
      have h₁ : Nat.factorization 144 2 = 4 := by
        rw [this, Nat.factorization_mul_apply_of_coprime]
        repeat rw [Nat.factorization_pow]
        norm_num
        norm_num
      
      have h₂ : Nat.factorization 144 3 = 2 := by
        rw [this, Nat.factorization_mul_apply_of_coprime]
        repeat rw [Nat.factorization_pow]
        norm_num
        norm_num

      rw [h₁, h₂]
      norm_num
    · have : 324 = 2^2 * 3^4 := by norm_num
      
      have h₁ : Nat.factorization 324 2 = 2 := by
        rw [this, Nat.factorization_mul_apply_of_coprime]
        repeat rw [Nat.factorization_pow]
        norm_num
        norm_num
      
      have h₂ : Nat.factorization 324 3 = 4 := by
        rw [this, Nat.factorization_mul_apply_of_coprime]
        repeat rw [Nat.factorization_pow]
        norm_num
        norm_num

      rw [h₁, h₂]
      norm_num
    
    decide
    exact pow_ne_zero 2 hn_neq_0
    exact hn_neq_0
