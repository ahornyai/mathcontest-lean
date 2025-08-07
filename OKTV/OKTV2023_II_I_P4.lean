import Mathlib.Tactic

/-
OKTV 2023/2024, II. kategória, I. forduló, 4. feladat:

Legyen d(M) a pozitív egész M szám összes pozitív osztóinak száma, beleszámolva az 1-et és magát M -et is.
Egy 2023-nál kisebb pozitív egész n számot pontosan két prím oszt, a 2 és a 3.
Mi lehet n, ha
d(n^2) = d(2*n) + d(3*n) + 13
--
bizonyítsuk be, hogy az egyetlen megoldás: n=576
-/
lemma eq_of_mul_eq_33 {x y : ℤ} (hxgeq0 : x ≥ 0) (hygeq0 : y ≥ 0) (h : x * y = 33) :
    x = 1 ∧ y = 33 ∨ x = 3 ∧ y = 11 ∨ x = 11 ∧ y = 3 ∨ x = 33 ∧ y = 1 := by
  have x_nat : ∃ n : ℕ, x = n := ⟨Int.natAbs x, by rw [Int.natAbs_of_nonneg hxgeq0]⟩
  have y_nat : ∃ n : ℕ, y = n := ⟨Int.natAbs y, by rw [Int.natAbs_of_nonneg hygeq0]⟩

  obtain ⟨x, rfl⟩ := x_nat
  obtain ⟨y, rfl⟩ := y_nat
  norm_cast at *

  have h₁ : (x, y) ∈ Nat.divisorsAntidiagonal 33 := by simpa using h
  have h₂ : Nat.divisorsAntidiagonal 33 = {(1, 33), (3, 11), (11, 3), (33, 1)} := by rfl
  simpa [h₂] using h₁

lemma deduct_x_y_vals {x y : ℕ} (h : 2^x * 3^y = 2^6 * 3^2) : x = 6 ∧ y = 2 := by
  apply And.intro
  · have coprime_1 : Nat.Coprime (2^x) (3^2) := by exact Nat.Coprime.pow x 2 rfl
    have coprime_2 : Nat.Coprime (2^6) (3^y) := by exact Nat.Coprime.pow 6 y rfl

    have : 2^x ∣ 2^6*3^2 := by exact Dvd.intro (3 ^ y) h
    have h1: 2^x ∣ 2^6 := by exact Nat.Coprime.dvd_of_dvd_mul_left coprime_1 this

    have : 2^6 ∣ 2^x*3^y := by exact Dvd.intro (3 ^ 2) (id (Eq.symm h))
    have h2: 2^6 ∣ 2^x := by exact Nat.Coprime.dvd_of_dvd_mul_right coprime_2 this

    have h3: 2^6=2^x := by exact Nat.dvd_antisymm h2 h1
    have h4: 2^6=2^x ↔ 6=x := by
      refine Nat.pow_right_inj ?_
      norm_num
    rw [h4] at h3
    exact h3.symm
  · have coprime_1 : Nat.Coprime (3^y) (2^6) := by exact Nat.Coprime.pow y 6 rfl
    have coprime_2 : Nat.Coprime (3^2) (2^x) := by exact Nat.Coprime.pow 2 x rfl

    have : 3^y ∣ 2^6*3^2 := by exact Dvd.intro_left (2 ^ x) h
    have h1: 3^y ∣ 3^2 := by exact Nat.Coprime.dvd_of_dvd_mul_left coprime_1 this

    have : 3^2 ∣ 3^y*2^x := by
      rw [Nat.mul_comm (3 ^ y) (2 ^ x)]
      exact Dvd.intro_left (2 ^ 6) (id (Eq.symm h))
    have h2: 3^2 ∣ 3^y := by exact Nat.Coprime.dvd_of_dvd_mul_right coprime_2 this

    have h3: 3^2=3^y := by exact Nat.dvd_antisymm h2 h1
    have h4: 3^2=3^y ↔ 2=y := by
      refine Nat.pow_right_inj ?_
      norm_num
    rw [h4] at h3
    exact h3.symm

theorem oktv2023_ii_i_iv (n x y : ℕ) (hx_nonzero : x ≠ 0) (hy_nonzero : y ≠ 0) (hn : n = 2^x*3^y) (hn_pos : 0 < n) (hn_le_2023 : n < 2023)
  : (n^2).divisors.card = (2*n).divisors.card + (3*n).divisors.card + 13 ↔ n = 2^6*3^2 := by
  have n_nonzero : n ≠ 0 := by exact Nat.not_eq_zero_of_lt hn_pos
  have n_sq_nonzero : n^2 ≠ 0 := by exact pow_ne_zero 2 n_nonzero

  have hn_primefacs : (n).primeFactors = {2,3} := by
      rw [hn, Nat.primeFactors_mul, Nat.primeFactors_pow, Nat.primeFactors_pow]
      norm_num
      rfl
      exact hy_nonzero
      exact hx_nonzero
      exact Ne.symm (NeZero.ne' (2 ^ x))
      exact Ne.symm (NeZero.ne' (3 ^ y))

  have hn_sq_primefacs : (n^2).primeFactors = {2,3} := by
    rw [Nat.primeFactors_pow]
    exact hn_primefacs
    norm_num

  have h2n_primefacs : (2*n).primeFactors = {2,3} := by
    rw [Nat.primeFactors_mul, hn_primefacs]
    norm_num
    rfl
    norm_num
    exact n_nonzero

  have h3n_primefacs : (3*n).primeFactors = {2,3} := by
    rw [Nat.primeFactors_mul, hn_primefacs]
    repeat norm_num
    exact n_nonzero

  constructor
  · intro h
    repeat rw [Nat.card_divisors] at h
    rw [hn_sq_primefacs, h2n_primefacs, h3n_primefacs, hn] at h
    norm_num at *

    have : ((2*x - 1)*(2*y - 1) : ℤ) = 33 := by linarith

    have left_fact_geq_0 : (2*x - 1 : ℤ) ≥ 0 := by omega
    have right_fact_geq_0 : (2*y - 1 : ℤ) ≥ 0 := by omega

    rcases eq_of_mul_eq_33 left_fact_geq_0 right_fact_geq_0 this with (⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩)
    · have : x=1 := by linarith
      rw [this] at hn

      have : y=17 := by linarith
      rw [this] at hn

      rw [hn] at hn_le_2023
      contradiction
    · have : x=2 := by linarith
      rw [this] at hn

      have : y=6 := by linarith
      rw [this] at hn

      rw [hn] at hn_le_2023
      contradiction
    · have : x=6 := by linarith
      rw [this] at hn

      have : y=2 := by linarith
      rw [this] at hn

      norm_num at hn
      exact hn
    · have : x=17 := by omega
      rw [this] at hn

      have : y=1 := by linarith
      rw [this] at hn

      rw [hn] at hn_le_2023
      contradiction
    omega
    omega
    exact n_sq_nonzero
  · intro h
    have hcoprime_2_3: Nat.Coprime 2 3 := by norm_num

    have : x=6 ∧ y=2 := by
      rw [hn] at h
      exact deduct_x_y_vals h
    obtain ⟨x, y⟩ := this

    have : (n^2).divisors.card = 65 := by
      rw [Nat.card_divisors, hn_sq_primefacs, hn]
      norm_num at *
      rw [x, y]
      norm_num
      exact n_sq_nonzero
    rw [this]

    have : (2*n).divisors.card = 24 := by
      rw [Nat.card_divisors, h2n_primefacs, hn]
      norm_num at *
      rw [x, y]
      norm_num
      linarith
    rw [this]

    have : (3*n).divisors.card = 28 := by
      rw [Nat.card_divisors, h3n_primefacs, hn]
      norm_num at *
      rw [x, y]
      norm_num
      linarith
    rw [this]
