import Mathlib.Tactic

example {l : ℕ} : 2 ^ (2 * l + 1 + 3) % 3 = 1 := by
  have : 2 ^ (2 * l + 1 + 3) = 2 ^ (2 * l + 4) := by norm_num
  rw [this]

  have : 2 ^ (2 * l + 2*2) = (2^2) ^ (l + 2) := by exact Nat.pow_mul 2 2 (l+2)
  rw [this]

  rw [Nat.pow_mod (2^2) (l+2) 3]
  norm_num

theorem eq_of_mul_eq_17 {x y : ℤ} (hxpos : x ≥ 0) (h : x * y = 17) :
  x = 1 ∧ y = 17 ∨ x = 17 ∧ y = 1 := by

  have h_div : x ∣ 17 := by
    use y
    omega

  have h_cases : x = 1 ∨ x = 17 := by
    have h_prime : Nat.Prime 17 := by norm_num
    have prime_divs := Nat.Prime.divisors h_prime

    have x_nat : ∃ n : ℕ, x = n := ⟨Int.natAbs x, by rw [Int.natAbs_of_nonneg hxpos]⟩

    obtain ⟨n, rfl⟩ := x_nat
    have : n ∣ 17 := by exact Int.ofNat_dvd.mp h_div

    norm_cast
    exact (Nat.dvd_prime h_prime).mp this

  cases h_cases with
  | inl hx =>
    left
    constructor
    · exact hx
    · rw [hx] at h
      simpa using h
  | inr hx =>
    right
    constructor
    · exact hx
    · rw [hx] at h
      have : 17 * y = 17 * 1 := by rw [h, mul_one]
      exact mul_left_cancel₀ (by norm_num) this

example {l : ℕ} (h : 2 ^ (l + 2) = 2^3) : l=1 := by
  have : 2 ≤ 2 := by norm_num
  have : l+2=3 := by
    apply Eq.symm
    exact (Nat.pow_right_inj this).mp (id (Eq.symm h))

  omega

/-
2017 emelt matek május - 5. feladat
Igazolja (teljes indukcióval vagy más módszerrel),
hogy 4^n+6n-1 minden n pozitív egész szám esetén osztható 9-cel!

I. megoldás: mod 3 megnézzük a maradékokat
-/
theorem erettsegi_2017_maj_5 (n : ℕ) (hnpos : n > 0) : 9 ∣ (4^n+6*n-1) := by
  have h4_pow_mod_3 {x : ℕ}: 4^x % 3 = 1 := by
    rw [Nat.pow_mod 4 x 3]
    norm_num

  mod_cases h: n%3
  · unfold Nat.ModEq at h
    have : 3 ∣ n := by exact Nat.dvd_of_mod_eq_zero h

    obtain ⟨k, hk⟩ := this
    rw [hk]

    have h4_pow_3k_mod_9 : 4^(3*k) % 9 = 1 := by
      have : 4^(3*k) = (4^3)^k := by exact Nat.pow_mul 4 3 k
      rw [this]

      have : (4 ^ 3) ^ k % 9 = 1 := by
        rw [Nat.pow_mod (4^3) k 9]
        norm_num
      rw [this]

    have : (4^(3*k) + 6*(3*k) - 1) % 9 = 0 := by omega

    refine Nat.dvd_of_mod_eq_zero ?_
    omega
  · unfold Nat.ModEq at h
    norm_num at h

    have : 3 ∣ n-1 := by exact (Nat.modEq_iff_dvd' hnpos).mp (id (Eq.symm h))
    have : ∃k : ℕ, n = 3 * k + 1 := by
      use (n-1)/3
      omega

    obtain ⟨k, hk⟩ := this
    rw [hk]

    have h4_pow_3k_mod_9 : 4^(3*k+1) % 9 = 4 := by
      have : 4^(3*k+1) = (4^3)^k * 4 := by
        rw [Nat.pow_succ]
        rw [Nat.pow_mul 4 3 k]

      rw [this]

      have : (4 ^ 3) ^ k % 9 = 1 := by
        rw [Nat.pow_mod (4^3) k 9]
        norm_num

      rw [Nat.mul_mod]
      rw [this]

    have : (4^(3*k+1) + 6*(3*k+1) - 1) % 9 = 0 := by omega

    refine Nat.dvd_of_mod_eq_zero ?_
    exact this
  · unfold Nat.ModEq at h
    norm_num at h

    have n_neq_1: n ≠ 1 := by
      by_contra!
      rw [this] at h
      contradiction

    have n_gt_1 : n > 1 := by exact Nat.lt_of_le_of_ne hnpos (id (Ne.symm n_neq_1))

    have : 3 ∣ n-2 := by exact (Nat.modEq_iff_dvd' n_gt_1).mp (id (Eq.symm h))
    have : ∃k : ℕ, n = 3 * k + 2 := by
      use (n-2)/3
      omega

    obtain ⟨k, hk⟩ := this
    rw [hk]

    have h4_pow_3k_mod_9 : 4^(3*k+2) % 9 = 7 := by
      have : 4^(3*k+2) = (4^3)^k * 16 := by
        rw [Nat.pow_succ]
        rw [Nat.pow_succ]
        rw [Nat.pow_mul 4 3 k]
        omega

      rw [this]

      have : (4 ^ 3) ^ k % 9 = 1 := by
        rw [Nat.pow_mod (4^3) k 9]
        norm_num

      rw [Nat.mul_mod]
      rw [this]

    have : (4^(3*k+2) + 6*(3*k+2) - 1) % 9 = 0 := by omega

    refine Nat.dvd_of_mod_eq_zero ?_
    exact this

/-
oldjuk meg ugyan ezt a feladatot indukcióval
-/
theorem erettsegi_2017_maj_5_indukcio (n : ℕ) : 9 ∣ (4^n+6*n-1) := by
  induction n with
  | zero => norm_num
  | succ n ih =>
    have : 4 ^ (n + 1) + 6 * (n + 1) - 1 = (3*4^n + 6) + (4^n + 6*n - 1) := by
      by_cases h': n=0
      · rw [h']
        norm_num
      · omega

    omega

theorem erettsegi_2025_onyp (n : ℕ) : 5 ∣ (7^n - 2^n) := by
  induction n with
  | zero => norm_num
  | succ n ih =>
    /-
    feltételezett: 5 | 7^n - 2^n
    5 | 7^(n+1) - 2^(n+1)

    7*7^n - 2*2^n = 5*7^n + 2*7^n - 2*2^n = 2*(7^n - 2^n) + 5*7^n
    -/
    have : 7^(n+1) - 2^(n+1) = 7^n*5 + (7^n - 2^n)*2 := by
      simp [Nat.pow_succ]
      rw [Nat.mul_sub_right_distrib]
      refine (Nat.sub_eq_iff_eq_add ?_).mpr ?_
      refine Nat.mul_le_mul ?_ ?_
      refine Nat.pow_le_pow_left ?_ n
      all_goals norm_num
      ring_nf

      have : 7 ^ n * 2 - 2 ^ n * 2 + 2 ^ n * 2 = 7^n*2 := by
        refine Nat.sub_add_cancel ?_
        refine Nat.mul_le_mul ?_ ?_
        refine Nat.pow_le_pow_left ?_ n
        repeat norm_num

      rw [this]
      ring_nf

    omega

example (p : ℕ) (hp : Prime p) (hp_neq_3_and_5 : p≠3 ∧ p≠5) : 360 ∣ (p^4 - 5*p^2 + 4 : ℤ) := by {
  ---have : (p^4 - 5*p^2 + 4 : ℤ) = (p^2 - 1)*(p^2 - 4) := by ring
  have : (p^4 - 5*p^2 + 4 : ℤ) = (p - 1)*(p + 1)*(p - 2)*(p+2) := by ring

  rw [this]

  obtain ⟨hp_neq_3, hp_neq_5⟩ := hp_neq_3_and_5

  by_cases h: p > 5
  · sorry
  · norm_num at h
    match p with
    | 2 => norm_num
    | 4 =>
      exfalso
      have : ¬Prime 4 := by
        refine IsSquare.not_prime ?_
        refine (isSquare_iff_exists_sq 4).mpr ?_
        use 2
        norm_num

      contradiction
    | p+6 => contradiction
}

example (p : ℕ) (hp : 3 ≤ p) (test : 360 ∣ (p-1 : ℕ)*(p-2 : ℕ)*(p-3 : ℕ)) : 360 ∣ (p - 1 : ℤ)*(p-2 : ℤ)*(p-3 : ℤ) := by
  have h_coe : ((p - 1 : ℤ) * (p - 2 : ℤ)*(p-3 : ℤ)) = ↑((p - 1)*(p - 2)*(p-3)) := by
    rw [Int.ofNat_mul]
    rw [Int.ofNat_sub (by linarith)]
    rw [Int.ofNat_mul]
    rw [Int.ofNat_sub (by linarith)]
    rw [Int.ofNat_sub (by linarith)]
    norm_cast

  rw [h_coe]
  -- Now apply the forward direction: ℕ divisibility ⇒ ℤ divisibility
  exact Int.ofNat_dvd_right.mpr test

lemma two_pow_mul_odd (x y : ℕ) (h₁ : Even x) (h₂ : Odd y)
  : ∀ b, 2^b = x * y → y = 1 := by
  intro b
  rintro heq
  by_contra! hy

  obtain ⟨a, ha⟩ := h₁

  have ha : x = 2 * a := by omega

  have a_neq_zero : a ≠ 0 := by
    by_contra!
    rw [this] at ha
    rw [ha] at heq
    norm_num at heq

  have y_neq_zero : y ≠ 0 := by
    by_contra!
    rw [this] at heq
    norm_num at heq

  have b_neq_zero : b ≠ 0 := by
    by_contra! hb

    rw [hb] at heq
    norm_num at heq
    rw [ha] at heq

    have : y * (2 * a) > 1 := by
      refine Right.one_lt_mul_of_le_of_lt ?_ ?_
      repeat omega

    linarith

  have b_pos : b ≥ 1 := by omega

  have h_div_y : y ∣ 2^b := by exact Dvd.intro_left x (id (Eq.symm heq))

  obtain ⟨k, hk⟩ := h₂

  have coprime : Nat.Coprime (2 * k + 1) (2^b) := by
      apply Nat.Coprime.symm
      refine Nat.Coprime.pow_left b ?_
      exact (Nat.coprime_mul_left_add_right 2 1 k).mpr rfl

  rw [← hk, Nat.coprime_iff_gcd_eq_one] at coprime

  have y_dvd_one : y ∣ 1 := by
    refine Nat.dvd_one.mpr ?_
    exact Nat.Coprime.eq_one_of_dvd coprime h_div_y

  have y_eq_one : y = 1 := by exact Nat.eq_one_of_dvd_one y_dvd_one

  contradiction


example (x y : ℕ) (x_neq_zero : x ≠ 0) (h : 2^x = 2*y) : 2^(x-1) = y := by
  -- Since x ≠ 0, x must be at least 1, so x-1 is a natural number.
  have x_pos : x ≥ 1 := Nat.pos_of_ne_zero x_neq_zero
  -- Rewrite x as (x-1)+1 to use exponentiation properties
  have hx : x = (x - 1) + 1 := by rw [Nat.sub_add_cancel x_pos]
  -- Substitute x in the hypothesis h
  rw [hx, pow_succ] at h
  omega
