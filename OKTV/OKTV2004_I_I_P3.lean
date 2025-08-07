import Mathlib.Tactic
/-
OKTV 2004/2005, I. kategória, I. forduló, 3. feladat:

Oldja meg az x^2*y^2 - 7*x*y^2 + 10*y^2 + 44*x*y - 154*y + 484 = 0
egyenletet, ha x és y pozitív prímszámok
----------
Bizonyítsuk, hogy az egyetlen megoldás x=3, y=11
-/
theorem oktv2004_i_i_iii (x y : ℤ) (hx_pos : x > 0) (hy_pos : y > 0) (hx_prime : Prime x) (hy_prime : Prime y) : x^2*y^2 - 7*x*y^2 + 10*y^2 + 44*x*y - 154*y + 484 = 0 ↔ x=3 ∧ y=11 := by
  constructor
  · intro h

    have : x ^ 2 * y ^ 2 - 7 * x * y ^ 2 + 10 * y ^ 2 + 44 * x * y - 154 * y = y * (x^2*y - 7*x*y + 10*y + 44*x - 154) := by ring
    rw [this] at h

    have : y * (x ^ 2 * y - 7 * x * y + 10 * y + 44 * x - 154) = -484 := by exact (Int.add_left_inj 484).mp h
    have h484_div_y : y ∣ 484 := by
      refine Int.dvd_neg.mp ?_
      exact Dvd.intro (x ^ 2 * y - 7 * x * y + 10 * y + 44 * x - 154) this

    have x_nat : ∃ n : ℕ, x = n := ⟨Int.natAbs x, by rw [Int.natAbs_of_nonneg (Int.le_of_lt hx_pos)]⟩
    have y_nat : ∃ n : ℕ, y = n := ⟨Int.natAbs y, by rw [Int.natAbs_of_nonneg (Int.le_of_lt hy_pos)]⟩

    obtain ⟨x, rfl⟩ := x_nat
    obtain ⟨y, rfl⟩ := y_nat

    norm_cast at h484_div_y

    have y_primefac : y ∈ Nat.primeFactors 484 := by
      refine (Nat.mem_primeFactors_of_ne_zero ?_).mpr ?_
      norm_num
      refine And.symm ⟨h484_div_y, ?_⟩
      exact Nat.prime_iff_prime_int.mpr hy_prime

    have h484_primefacs : Nat.primeFactors 484 = {2, 11} := by
      have : 484 = 2^2*11^2 := by norm_num
      rw [this, Nat.primeFactors_mul]
      repeat rw [Nat.primeFactors_prime_pow]
      all_goals norm_num
      rfl

    have : y ∈ ({2, 11} : Finset ℕ) := by
      rw [← h484_primefacs]
      exact y_primefac

    have : y = 2 ∨ y = 11 := by exact List.mem_pair.mp this

    rcases this with h1 | h1
    · rw [h1] at h

      have : (x^2 + 15*x + 54 : ℤ) = 0 := by omega
      have : ((x+6)*(x+9) : ℤ) = 0 := by linarith

      have : (x+6 : ℤ) = 0 ∨ (x+9 : ℤ) = 0 := by exact Int.mul_eq_zero.mp this
      have : (x : ℤ) = -6 ∨ (x : ℤ) = -9 := by omega

      rcases this with h2 | h2
      all_goals contradiction
    · rw [h1] at h

      have : (x^2 - 3*x : ℤ) = 0 := by omega
      have : (x*(x-3) : ℤ) = 0 := by linarith

      have : (x : ℤ)=0 ∨ (x-3 : ℤ)=0 := by exact Int.mul_eq_zero.mp this

      rcases this with h2 | h2
      · rw [h2] at hx_prime
        norm_num at hx_prime
      · have : (x : ℤ) = 3 := by exact (Int.sub_left_inj 3).mp h2

        exact ⟨this, congrArg Nat.cast h1⟩
  · intro h
    obtain ⟨rfl, rfl⟩ := h
    norm_num
