import Mathlib.Tactic
import Mathlib.Algebra.Group.Even

/-
OKTV 2011/2012, III. kategória, I. forduló, 3. feladat:

Mely k és n pozitív egészekre teljesül: |2^k − 3^n| = 17
-/
lemma not_pow_3_19 : ¬ ∃ n, 3 ^ n = 19 := by
  intro ⟨n, hn⟩
  have h1 : 3^2 < 3^n := by
    rw [hn]
    norm_num
  have h2 : 3^n < 3^3 := by
    rw [hn]
    norm_num

  have h3 : 2 < n := Nat.pow_lt_pow_iff_right (by norm_num) |>.mp h1
  have h4 : n < 3 := Nat.pow_lt_pow_iff_right (by norm_num) |>.mp h2

  omega

lemma not_pow_3_21 : ¬ ∃ n, 3 ^ n = 21 := by
  intro ⟨n, hn⟩
  have h1 : 3^2 < 3^n := by
    rw [hn]
    norm_num
  have h2 : 3^n < 3^3 := by
    rw [hn]
    norm_num

  have h3 : 2 < n := Nat.pow_lt_pow_iff_right (by norm_num) |>.mp h1
  have h4 : n < 3 := Nat.pow_lt_pow_iff_right (by norm_num) |>.mp h2

  omega

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

theorem oktv_2011_iii_3 (n k : ℕ) (hnpos : n > 0) (hkpos : k > 0) : n=4 ∧ k=6 ↔ abs ((2^k - 3^n : ℤ)) = 17 := by
  constructor
  · intro h
    obtain ⟨rfl,rfl⟩ := h
    norm_num
  · intro h
    match k with
    | 0 => contradiction
    | 1 =>
      norm_num at h

      cases' abs_cases (2 - 3^n : ℤ) with h₂ h₂
      · rw [h] at h₂
        obtain ⟨h₃, h₄⟩ := h₂
        have : 0 ≤ (2 - 3 ^ n : ℤ) ↔ 3 ^ n ≤ 2 := by
          constructor
          · intro x
            linarith
          · omega

        rw [this] at h₄

        have : 3^n ≥ 3^1 := by
          refine Nat.pow_le_pow_of_le_right ?_ hnpos
          norm_num

        omega
      · obtain ⟨h₃, h₄⟩ := h₂
        rw [h₃] at h

        have : -(2 - 3 ^ n) = 3^n-2 := by ring_nf
        rw [this] at h

        have : 3^n = 19 := by linarith
        have h' : ∃ n, 3^n = 19 := ⟨n, this⟩
        have h'_contra: ¬ ∃ n, 3 ^ n = 19 := by exact not_pow_3_19

        exact False.elim (h'_contra h')
    | 2 =>
      norm_num at h

      cases' abs_cases (4 - 3^n : ℤ) with h₂ h₂
      · rw [h] at h₂
        obtain ⟨h₃, h₄⟩ := h₂
        have : 0 ≤ (4 - 3 ^ n : ℤ) ↔ 3 ^ n ≤ 2 := by
          constructor
          · intro x
            linarith
          · omega

        rw [this] at h₄

        have : 3^n ≥ 3^1 := by
          refine Nat.pow_le_pow_of_le_right ?_ hnpos
          norm_num

        omega
      · obtain ⟨h₃, h₄⟩ := h₂
        rw [h₃] at h

        have : -(4 - 3 ^ n) = 3^n-4 := by ring_nf
        rw [this] at h

        have : 3^n = 21 := by linarith
        have h' : ∃ n, 3^n = 21 := ⟨n, this⟩
        have h'_contra: ¬ ∃ n, 3 ^ n = 21 := by exact not_pow_3_21

        exact False.elim (h'_contra h')
    | k+3 =>
      have : 2^(k+3) = 2^3*2^k := by exact Nat.pow_add' 2 k 3
      have lhs_mod_8 : 2^(k+3) % 8 = 0 := by
        rw [this]
        exact Nat.mul_mod_right (2 ^ 3) (2 ^ k)

      cases' abs_cases (2^(k+3) - 3^n : ℤ) with h₂ h₂
      · obtain ⟨h₃, h₄⟩ := h₂
        rw [h₃] at h

        mod_cases h': n%2
        · unfold Nat.ModEq at h'
          have : 2∣n := by exact Nat.dvd_of_mod_eq_zero h'
          obtain ⟨m, hm⟩ := this
          rw [hm] at h

          have : 3^(2*m) = 9^m := by exact Mathlib.Tactic.Ring.pow_nat rfl rfl rfl
          have : 9^m % 8 = (9%8)^m % 8 := by exact Nat.pow_mod 9 m 8
          have : 9^m % 8 = 1 := by
            rw [this]
            norm_num
          have three_pow_2m_mod_8 : 3^(2*m)%8 = 1 := by omega

          have : (2 ^ (k + 3) - 3 ^ (2 * m): ℤ) = 17 ↔ 2 ^ (k + 3) = 17 + 3 ^ (2 * m) := by
            constructor
            · intro h
              have : (2 ^ (k + 3) - 3 ^ (2 * m) : ℤ) = (2 ^ (k + 3) - 3 ^ (2 * m) : ℕ) := by
                rw [Int.ofNat_sub (by linarith)]
                norm_cast

              omega
            · omega

          rw [this] at h

          have rhs_mod_8 : ((17%8)+(3^(2 * m))%8)%8 = 2 := by
            rw [three_pow_2m_mod_8]

          omega
        · unfold Nat.ModEq at h'
          have : ∃m : ℕ, n = 2 * m + 1 := by
            use (n-1)/2
            ring_nf
            have : (n - 1) / 2 * 2 = n-1 := by
              refine Nat.div_mul_cancel ?_
              exact (Nat.modEq_iff_dvd' hnpos).mp (id (Eq.symm h'))
            rw [this]
            omega

          obtain ⟨m,hm⟩ := this
          rw [hm] at h

          have : 3^(2*m+1) = 3*3^(2*m) := by exact Nat.pow_succ'
          have : 3^(2*m) = 9^m := by exact Mathlib.Tactic.Ring.pow_nat rfl rfl rfl
          have : 9^m % 8 = (9%8)^m % 8 := by exact Nat.pow_mod 9 m 8
          have : 9^m % 8 = 1 := by
            rw [this]
            norm_num
          have three_pow_2m_plus_1_mod_8 : 3^(2*m+1)%8 = 3 := by omega

          have : (2 ^ (k + 3) - 3 ^ (2 * m + 1): ℤ) = 17 ↔ 2 ^ (k + 3) = 17 + 3 ^ (2 * m + 1) := by
            constructor
            · intro h
              have : (2 ^ (k + 3) - 3 ^ (2 * m + 1) : ℤ) = (2 ^ (k + 3) - 3 ^ (2 * m + 1) : ℕ) := by
                rw [Int.ofNat_sub (by linarith)]
                norm_cast

              omega
            · omega

          rw [this] at h
          have rhs_mod_8 : ((17%8)+(3^(2 * m+1))%8)%8 = 4 := by
            rw [three_pow_2m_plus_1_mod_8]

          omega
      · obtain ⟨h₃, h₄⟩ := h₂
        rw [h₃] at h

        have : -(2 ^ (k + 3) - 3 ^ n) = 3 ^ n - 2 ^ (k + 3) := by linarith
        rw [this] at h

        mod_cases h': n%2
        · unfold Nat.ModEq at h'
          have : 2∣n := by exact Nat.dvd_of_mod_eq_zero h'
          obtain ⟨m, hm⟩ := this
          rw [hm] at h

          mod_cases hk': k%2
          · unfold Nat.ModEq at hk'
            have : 2∣k := by exact Nat.dvd_of_mod_eq_zero hk'
            obtain ⟨l, hl⟩ := this

            rw [hl] at h

            --wrong case
            have three_pow_2m_mod_3 : 3^(2*m)%3 = 0 := by
              refine Nat.mod_eq_zero_of_dvd ?_
              refine dvd_pow_self 3 ?_
              omega

            have two_pow_2l_plus_3_mod_3 : 2 ^ (2 * l + 3) % 3 = 2 := by
              rw [Nat.pow_succ]
              rw [Nat.mul_mod]

              have : 2^(2*l+2) = 2^(2*(l+1)) := by exact rfl
              rw [this]
              rw [Nat.pow_mul 2 2 (l+1)]
              rw [Nat.pow_mod (2^2) (l+1) 3]
              norm_num

            have : (3 ^ (2*m) - 2 ^ (2 * l + 3): ℤ) = 17 ↔ 3 ^ (2*m) = 17 + 2 ^ (2 * l + 3) := by
              constructor
              · intro h
                have : (3 ^ (2*m) - 2 ^ (2 * l + 3) : ℤ) = (3 ^ (2*m) - 2 ^ (2 * l + 3) : ℕ) := by
                  rw [Int.ofNat_sub (by linarith)]
                  norm_cast

                omega
              · omega

            rw [this] at h
            have rhs_mod_8 : ((17%3)+(2 ^ (2 * l + 3))%3)%3 = 1 := by
              rw [two_pow_2l_plus_3_mod_3]

            omega
          · unfold Nat.ModEq at hk'
            have : ∃l : ℕ, k = 2 * l + 1 := by
              use (k-1)/2

              have : k ≠ 0 := by
                by_contra!
                rw [this] at hk'
                norm_num at hk'

              have : (k - 1) / 2 * 2 = k-1 := by
                refine Nat.div_mul_cancel ?_
                refine (Nat.modEq_iff_dvd' ?_).mp (id (Eq.symm hk'))
                exact Nat.one_le_iff_ne_zero.mpr this

              omega

            obtain ⟨l,hl⟩ := this
            rw [hl] at h

            --correct case
            have : 2 * l + 1 + 3 = 2*(l+2) := by ring_nf
            rw [this] at h

            have : (3: ℤ) ^ (2 * m) = (3^m)^2 := by exact pow_mul' 3 2 m
            rw [this] at h

            have : (2 : ℤ) ^ (2 * (l + 2)) = (2 ^ (l + 2))^2 := by exact pow_mul' 2 2 (l + 2)
            rw [this] at h

            rw [sq_sub_sq] at h

            have right_fac_geq_0 : ((3 : ℤ) ^ m + (2 : ℤ) ^ (l + 2)) ≥ 0 := by
              norm_cast
              exact Nat.le_add_left 0 ((3 ^ m).add (2 ^ (l + 2)))

            rcases eq_of_mul_eq_17 right_fac_geq_0 h with (⟨x, y⟩ | ⟨x, y⟩)
            · have : 3^m = 3^2 := by linarith
              have : m = 2 := by
                have two_leq_3 : 2 ≤ 3 := by norm_num

                apply Eq.symm
                exact (Nat.pow_right_inj two_leq_3).mp (id (Eq.symm this))

              rw [this] at x
              norm_num at x

              exfalso
              have : 2 ^ (l + 2) > 0 := by exact Nat.two_pow_pos (l + 2)
              have : 9 + 2 ^ (l + 2) ≠ 1 := by omega
              linarith
            · have : 3^m = 3^2 := by linarith
              have : m = 2 := by
                have two_leq_3 : 2 ≤ 3 := by norm_num

                apply Eq.symm
                exact (Nat.pow_right_inj two_leq_3).mp (id (Eq.symm this))

              rw [this] at hm
              rw [hm]
              norm_num

              rw [this] at x
              have : 2 ^ (l + 2) = 2^3 := by linarith
              have : l = 1 := by
                  have two_leq_two : 2 ≤ 2 := by norm_num
                  have : l+2=3 := by
                    apply Eq.symm
                    exact (Nat.pow_right_inj two_leq_two).mp (id (Eq.symm this))

                  omega

              rw [this] at hl
              rw [hl]
        · unfold Nat.ModEq at h'

          have : ∃m : ℕ, n = 2 * m + 1 := by
            use (n-1)/2
            ring_nf
            have : (n - 1) / 2 * 2 = n-1 := by
              refine Nat.div_mul_cancel ?_
              exact (Nat.modEq_iff_dvd' hnpos).mp (id (Eq.symm h'))
            rw [this]
            omega

          obtain ⟨m,hm⟩ := this
          rw [hm] at h

          have : 3^(2*m+1) = 3*3^(2*m) := by exact Nat.pow_succ'
          have : 3^(2*m) = 9^m := by exact Mathlib.Tactic.Ring.pow_nat rfl rfl rfl
          have : 9^m % 8 = (9%8)^m % 8 := by exact Nat.pow_mod 9 m 8
          have : 9^m % 8 = 1 := by
            rw [this]
            norm_num
          have three_pow_2m_plus_1_mod_8 : 3^(2*m+1)%8 = 3 := by omega

          have : (3 ^ (2 * m + 1) - 2 ^ (k + 3): ℤ) = 17 ↔ 3 ^ (2 * m + 1) = 17 + 2 ^ (k + 3) := by
            constructor
            · intro h
              have : (3 ^ (2 * m + 1) - 2 ^ (k + 3) : ℤ) = (3 ^ (2 * m + 1) - 2 ^ (k + 3) : ℕ) := by
                rw [Int.ofNat_sub (by linarith)]
                norm_cast

              omega
            · omega

          rw [this] at h

          have rhs_mod_8 : ((17%8)+(2 ^ (k + 3))%8)%8 = 1 := by
            rw [lhs_mod_8]

          omega
