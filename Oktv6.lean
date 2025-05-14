import Mathlib.Tactic
import Mathlib.Algebra.Group.Even

/-
OKTV 2019/2020, II. kategória, II. forduló, 3. feladat:

Határozzuk meg, mely egész n és m számokra teljesül az alábbi egyenlet:
n^5 + n^4 = 7^m − 1
---
Bizonyítsuk, hogy a megoldáshalmaz: {(-1, 0), (0, 0), (2, 2)}

egyértelmű, hogy m < 0 számok esetén a jobb oldal nem egész szám, még a bal oldal igen,
ezért értelmezzük a feladatot nemnegatív m-en az egyszerűség kedvéért
-/
def SolutionSet : Set (ℤ × ℕ) := {(-1, 0), (0, 0), (2, 2)}

theorem positive_int_to_nat {n : ℤ} (h_pos : n > 0) : ∃ (k : ℕ), n = k ∧ k > 0 := by
  use Int.natAbs n
  constructor
  · refine Int.eq_natAbs_of_zero_le ?_
    exact Int.le_of_lt h_pos
  · refine Int.natAbs_pos.mpr ?_
    apply ne_of_gt h_pos

lemma not_pow_7_3 : ¬ ∃ n, 7 ^ n = 3 := by
  intro ⟨n, hn⟩
  have h1 : 7^0 < 7^n := by
    rw [hn]
    norm_num
  have h2 : 7^n < 7^1 := by
    rw [hn]
    norm_num
  have h3 : 0 < n := Nat.pow_lt_pow_iff_right (by norm_num) |>.mp h1
  have h4 : n < 1 := Nat.pow_lt_pow_iff_right (by norm_num) |>.mp h2
  omega

lemma pow_7_m_is_49_iff : ∀ n, 49 = 7^n ↔ n = 2 := by
  intro n
  constructor
  · rintro h
    have h1 : 7^1 < 7^n := by
      rw [← h]
      norm_num
    have h2 : 7^n < 7^3 := by
      rw [← h]
      norm_num

    have h3 : 1 < n := Nat.pow_lt_pow_iff_right (by norm_num) |>.mp h1
    have h4 : n < 3 := Nat.pow_lt_pow_iff_right (by norm_num) |>.mp h2

    omega
  · exact fun a ↦ Eq.symm (Mathlib.Tactic.Ring.pow_congr rfl a rfl)

lemma pow_7_divisors {x y n : ℕ} (h₁ : x ∣ 7^n) (h₂ : y ∣ 7^n) (h₃ : x > 7) (h₄ : y > 7)
  : 7^2 ∣ x ∧ 7^2 ∣ y := by
  have prime_7 : Nat.Prime 7 := by exact Nat.properDivisors_eq_singleton_one_iff_prime.mp rfl

  obtain ⟨i, hik, rfl⟩ := (Nat.dvd_prime_pow prime_7).1 h₁
  obtain ⟨j, hik, rfl⟩ := (Nat.dvd_prime_pow prime_7).1 h₂

  have : 1 < 7 := by norm_num

  have one_lt_seven_pow_i : 7^1 < 7^i := by linarith
  have one_lt_seven_pow_j : 7^1 < 7^j := by linarith

  rw [Nat.pow_lt_pow_iff_right this] at one_lt_seven_pow_i
  rw [Nat.pow_lt_pow_iff_right this] at one_lt_seven_pow_j

  have seven_pow_i_geq_49 : 7^2 ≤ 7^i := by exact Nat.pow_le_pow_of_le this one_lt_seven_pow_i
  have seven_pow_j_geq_49 : 7^2 ≤ 7^j := by exact Nat.pow_le_pow_of_le this one_lt_seven_pow_j

  constructor
  · exact (Nat.pow_dvd_pow_iff_le_right this).mpr one_lt_seven_pow_i
  · exact (Nat.pow_dvd_pow_iff_le_right this).mpr one_lt_seven_pow_j

theorem oktv_2019_ii_3 (n : ℤ) (m : ℕ) :
  ⟨n, m⟩ ∈ SolutionSet ↔
  n^5 + n^4 = 7^m - 1 := by
  unfold SolutionSet
  constructor
  · intro h
    simp at h

    rcases h with h1 | h2 | h3
    · obtain ⟨rfl, rfl⟩ := h1
      norm_num
    · obtain ⟨rfl, rfl⟩ := h2
      norm_num
    · obtain ⟨rfl, rfl⟩ := h3
      norm_num
  · intro h
    have h1 : n^5 + n^4 + 1 = 7^m := by exact add_eq_of_eq_sub h
    have lhs_fact: (n^3 - n + 1) * (n^2 + n + 1) = n^5 + n^4 + 1 := by ring
    have h2 : (n^3 - n + 1) * (n^2 + n + 1) = 7^m := by linarith

    by_cases h3 : m = 0
    · rw [h3] at h
      norm_num at h

      have : n^5 + n^4 = n^4 * (n + 1) := by ring

      rw [h] at this
      rw [zero_eq_mul] at this
      rw [pow_eq_zero_iff (by norm_num : 4 ≠ 0)] at this -- n^4 = 0 ↔ n = 0

      rcases this with n_zero | n_plus_one_zero
      · rw [h3]
        rw [n_zero]
        norm_num
      · have : n = -1 := by linarith
        rw [this]
        rw [h3]
        norm_num
    · have h3 : m ≠ 0 := by exact h3
      have h4 : 0 < m := by exact Nat.zero_lt_of_ne_zero h3

      by_cases n_nonpos : n ≤ 0
      · have rhs_pos : 7^m - 1 > 0 := by
          refine Nat.sub_pos_of_lt ?_
          refine Nat.one_lt_pow h3 ?_
          norm_num

        have n_neq_zero : n ≠ 0 := by
          by_contra!
          rw [this] at h1
          norm_num at h1

          have h1 : 7^m = 1 := by linarith

          rw [Nat.pow_eq_one] at h1
          rcases h1 with seven_eq_one | m_zero
          · contradiction
          · contradiction

        have n_neg : n < 0 := by exact lt_of_le_of_ne n_nonpos n_neq_zero

        have abs_n_pow_5_geq_n_pow_4 : abs (n^5) ≥ abs (n^4) := by
          rw [abs_pow, abs_pow]
          refine pow_le_pow_right₀ ?_ ?_
          refine Int.one_le_abs ?_
          exact n_neq_zero
          norm_num

        have lhs_neg : n^5 + n^4 ≤ 0 := by
          -- When n < 0 and odd power, n^5 is negative
          have n_pow_5_neg : n ^ 5 < 0 := by
            refine Odd.pow_neg ?_ n_neg
            exact Nat.odd_iff.mpr rfl

          -- When n < 0 and even power, n^4 is positive
          have n_pow_4_pos : n ^ 4 > 0 := by exact pos_of_mul_neg_left n_pow_5_neg n_nonpos

          have abs_n_pow_5 : |n ^ 5| = -n ^ 5 := by apply abs_of_neg n_pow_5_neg
          have abs_n_pow_4 : |n ^ 4| = n ^ 4 := by apply abs_of_pos n_pow_4_pos

          have : n ^ 5 + n ^ 4 ≤ 0 := by linarith

          exact this

        exfalso
        rw [h] at lhs_neg

        have : (0 : ℤ) < 7 ^ m - 1 := by
          refine Int.sub_pos_of_lt ?_
          refine one_lt_pow₀ ?_ h3
          norm_num

        apply Int.not_le_of_gt this lhs_neg
      · have h_pos : n > 0 := by exact Int.lt_of_not_ge n_nonpos

        have ⟨k, n_eq_k, k_pos⟩ := positive_int_to_nat h_pos

        rw [n_eq_k] at h1
        norm_cast at h1

        match k with
        | 1 =>
          norm_num at h1

          have : 3 = 7 ^ m ↔  7 ^ m = 3 := by exact eq_comm

          have h_contra : ∃ k, 7 ^ k = 3 := by
            use m
            rw [← this]
            exact h1

          have h_contra' : ¬ ∃ k, 7 ^ k = 3 := by apply not_pow_7_3
          contradiction
        | 2 =>
          norm_num at h1

          have : 49 = 7 ^ m ↔ m = 2 := by exact pow_7_m_is_49_iff m

          rw [this] at h1
          rw [h1]
          rw [n_eq_k]
          norm_num
        | k+3 =>
          have k_plus_3_prime_gt_2 : k+3 > 2 := by linarith

          rw [n_eq_k] at h2
          norm_cast at h2

          have left_mul_simp : k^3 + 9*k^2 + 26*k + 25 = (((k + 3) ^ 3) : ℤ) - ((k + 3) : ℤ) + 1 := by linarith
          have right_mul_simp : k^2 + 7*k + 13 = (k + 3) ^ 2 + (k + 3) + 1 := by ring

          rw [Int.subNatNat_eq_coe] at h2
          push_cast at h2

          rw [← left_mul_simp] at h2
          norm_cast at h2

          rw [← right_mul_simp] at h2

          have left_fact_gt_7 : k ^ 3 + 9 * k ^ 2 + 26 * k + 25 > 7 := by omega
          have right_fact_gt_7 : k^2 + 7*k + 13 > 7 := by omega

          have left_fact_div : (k ^ 3 + 9 * k ^ 2 + 26 * k + 25) ∣ 7^m := by exact Dvd.intro (k^2 + 7*k + 13) h2
          have right_fact_div : (k^2 + 7*k + 13) ∣ 7^m := by exact Dvd.intro_left (k ^ 3 + 9 * k ^ 2 + 26 * k + 25) h2

          have both_fact_div_49 : 7^2 ∣ (k ^ 3 + 9 * k ^ 2 + 26 * k + 25) ∧ 7^2 ∣ (k^2 + 7*k + 13) := by
            exact pow_7_divisors left_fact_div right_fact_div left_fact_gt_7 right_fact_gt_7

          obtain ⟨left_fact_div_49, right_fact_div_49⟩ := both_fact_div_49

          /-
          n^3 - n + 1 = (n-1)(n^2 + n + 1) - (n-2)
                      = (k+3-1)((k+3)^2 + k+3 + 1) - (k+3-2)
                      = (k+2)(k^2 + 7*k + 13) - (k+1)
          => k+1 osztható 49

          n^2 + n + 1 = (n + 3)(n - 2) + 7
                      = (k+3+3)(k + 3 - 2) + 7
                      = (k+6)(k+1) + 7
          => 7 osztható 49, de ez ellentmondás!
          -/
          -- prove that k+1 is divisible by 49 (using the left factor)
          have left_fact_diff : k ^ 3 + 9 * k ^ 2 + 26 * k + 25 = (k+2)*(k^2 + 7*k + 13) - (k+1) := by
            calc
              _ = k^3 + 9*k^2 + 27*k + 26 - (k+1) := by omega
              _ = (k+2)*(k^2 + 7*k + 13) - (k+1) := by ring_nf

          have right_fact_diff : k^2 + 7*k + 13 = (k+6)*(k+1) + 7 := by ring_nf

          rw [left_fact_diff] at left_fact_div_49
          rw [right_fact_diff] at right_fact_div_49

          have right_fact_div_49' : 7^2 ∣ (k^2 + 7*k + 13) := by omega
          have left_fact_sub_div_49 : 7^2 ∣ (k+2)*(k^2 + 7*k + 13) := by exact Dvd.dvd.mul_left right_fact_div_49' (k + 2)
          have left_fact_sum : (k+2)*(k^2 + 7*k + 13) = ((k+2)*(k^2 + 7*k + 13) - (k+1)) + (k+1) := by omega

          rw [left_fact_sum] at left_fact_sub_div_49

          have k_plus_1_div_49 : 7^2 ∣ (k + 1) := by exact (Nat.dvd_add_iff_right left_fact_div_49).mpr left_fact_sub_div_49

          -- prove that 7 is divisible by 49 (this will lead to contradiction), let's use the fact that k+1 is divisible by 49
          have right_fact_left_div_49 : 7 ^ 2 ∣ (k + 6) * (k + 1) := by exact Dvd.dvd.mul_left k_plus_1_div_49 (k + 6)

          have h_7_div_49 : 7^2 ∣ 7 := by exact (Nat.dvd_add_iff_right right_fact_left_div_49).mpr right_fact_div_49

          -- 7^2 ∣ 7 is false, this leads to contradiction
          exfalso
          contradiction
