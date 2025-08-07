import Mathlib.Tactic

/-
OKTV 2021/2022, II. kategória, II. forduló, 1. feladat:

Határozzuk meg az összes olyan prímszámot, amely előáll ⌊n^2 / 5⌋ alakban,
ahol n pozitív egész számot jelöl.
-------
n ∈ {5, 4, 6} esete vezet kizárólag megoldáshoz p ∈ {5, 3, 7}, bizonyítsuk ezt
-/
theorem oktv2021_ii_ii_i (p : ℕ) (hp : Nat.Prime p) :
  (∃ n : ℕ, n > 0 ∧ p = ⌊(n^2 : ℚ) / 5⌋) ↔ p = 5 ∨ p = 3 ∨ p = 7 := by
  constructor

  -- egyik irány: ha p = ⌊n²/5⌋ valamilyen n > 0, akkor p = 3, 5 vagy 7
  · intro ⟨n, hn⟩
    mod_cases n % 5
    · refine Or.symm (Or.inr ?_)
      obtain ⟨n_pos, hn⟩ := hn

      rw [Nat.modEq_zero_iff_dvd] at H

      have h_n : ∃ k : ℕ, n = 5 * k := by exact H
      obtain ⟨k, hk⟩ := h_n

      have : (↑(5 * k)^2 / 5 : ℚ) = 5 * k^2 := by norm_num; linarith

      rw [hk] at hn
      rw [this] at hn

      have : ⌊5*(k : ℚ)^2⌋ = 5 * k^2 := by exact Int.floor_eq_iff.mpr ⟨by norm_num, by norm_num⟩
      rw [this] at hn

      have k_non_neg : k ≥ 0 := by omega

      have h_k_eq_one : k = 1 := by
        by_contra neq
        have k_neq_1 : k ≠ 1 := by exact neq
        have k_sq_neq_1 : k^2 ≠ 1 := by
          refine Ne.symm (Nat.ne_of_lt ?_)
          refine (one_lt_sq_iff₀ k_non_neg).mpr ?_
          omega

        have h_not_prime : ¬ Nat.Prime p := by
          norm_cast at hn
          rw [hn]

          refine Nat.not_prime_mul ?_ k_sq_neq_1
          exact Nat.succ_succ_ne_one 3

        contradiction

      rw [h_k_eq_one] at hn
      simp at hn
      norm_cast at hn
    · unfold Nat.ModEq at H
      norm_num at H

      have h_n : ∃k : ℕ, n = 5 * k + 1 := by
        use (n-1)/5
        refine Nat.eq_add_of_sub_eq ?_ ?_
        linarith
        refine Eq.symm (Nat.mul_div_cancel' ?_)
        refine (Nat.modEq_iff_dvd' ?_).mp (id (Eq.symm H))
        omega

      obtain ⟨k, hk⟩ := h_n
      obtain ⟨n_pos, hn⟩ := hn

      rw [hk] at hn

      have : ((5 * k + 1) ^ 2/5 : ℚ) = 5*k^2 + 2*k + 1/5 := by ring
      push_cast at hn
      rw [this] at hn

      have : ⌊(5*k^2 + 2*k + 1/5 : ℚ)⌋ = 5*k^2 + 2*k := by exact Int.floor_eq_iff.mpr ⟨by norm_num, by norm_num⟩
      rw [this] at hn

      by_cases h: k=1
      · rw [h] at hn
        omega
      · have : 5*k^2 + 2*k = k*(5*k + 2) := by ring
        have hn_prime: ¬ Nat.Prime p := by
          norm_cast at hn
          rw [hn]

          rw [this]
          refine Nat.not_prime_mul h ?_
          exact Ne.symm (Nat.ne_of_beq_eq_false rfl)

        contradiction
    · unfold Nat.ModEq at H
      norm_num at H

      obtain ⟨n_pos, hn⟩ := hn

      have hn_geq_2 : 2≤n := by
        by_contra!
        interval_cases n
        all_goals (
          norm_num at hn
          rw [hn] at hp
          trivial
        )

      have h_n : ∃k : ℕ, n = 5 * k + 2 := by
        use (n-2)/5
        refine Nat.eq_add_of_sub_eq ?_ ?_
        exact hn_geq_2
        refine Eq.symm (Nat.mul_div_cancel' ?_)
        refine (Nat.modEq_iff_dvd' ?_).mp (id (Eq.symm H))
        exact hn_geq_2

      obtain ⟨k, hk⟩ := h_n

      rw [hk] at hn

      have : ((5 * k + 2) ^ 2/5 : ℚ) = 5*k^2 + 4*k + 4/5 := by ring
      push_cast at hn
      rw [this] at hn

      have : ⌊(5*k^2 + 4*k + 4/5 : ℚ)⌋ = 5*k^2 + 4*k := by exact Int.floor_eq_iff.mpr ⟨by norm_num, by norm_num⟩
      rw [this] at hn

      by_cases h: k=1
      · rw [h] at hn
        norm_num at hn
        norm_cast at hn
        rw [hn] at hp
        contradiction
      · have : (5 * k ^ 2 + 4 * k : ℤ) = k*(5*k+4) := by ring
        rw [this] at hn

        have hn_prime: ¬ Nat.Prime p := by
          norm_cast at hn
          rw [hn]

          refine Nat.not_prime_mul h ?_
          exact Ne.symm (Nat.ne_of_beq_eq_false rfl)
        contradiction
    · unfold Nat.ModEq at H
      norm_num at H

      obtain ⟨n_pos, hn⟩ := hn

      have hn_geq_3 : 3≤n := by
        by_contra!
        interval_cases n
        all_goals (
          norm_num at hn
          rw [hn] at hp
          trivial
        )

      have h_n : ∃k : ℕ, n = 5 * k + 3 := by
        use (n-3)/5
        refine Nat.eq_add_of_sub_eq ?_ ?_
        exact hn_geq_3
        refine Eq.symm (Nat.mul_div_cancel' ?_)
        refine (Nat.modEq_iff_dvd' ?_).mp (id (Eq.symm H))
        exact hn_geq_3

      obtain ⟨k, hk⟩ := h_n

      rw [hk] at hn

      have : ((5 * k + 3) ^ 2/5 : ℚ) = 5*k^2 + 6*k + 9/5 := by ring
      push_cast at hn
      rw [this] at hn

      have : ⌊(5*k^2 + 6*k + 9/5 : ℚ)⌋ = 5*k^2 + 6*k + 1 := by
        apply Int.floor_eq_iff.mpr
        constructor
        · norm_num
        · norm_cast
          have : 5 * k ^ 2 + 6 * k + 1 + 1 = 5 * k ^ 2 + 6 * k + 2 := by ring
          rw [this]
          norm_num
      rw [this] at hn

      by_cases h: k=0
      · rw [h] at hn
        norm_num at hn
        rw [hn] at hp
        contradiction
      · have : (5*k^2 + 6*k + 1 : ℤ) = (5*k+1)*(k+1) := by ring
        rw [this] at hn

        have hn_prime: ¬ Nat.Prime p := by
          norm_cast at hn
          rw [hn]

          refine Nat.not_prime_mul ?_ ?_
          refine Nat.succ_ne_succ.mpr ?_
          refine Nat.mul_ne_zero ?_ h
          exact Ne.symm (Nat.zero_ne_add_one 4)
          exact Ne.symm ((fun {m n} ↦ Nat.succ_ne_succ.mpr) fun a ↦ h (id (Eq.symm a)))
        contradiction
    · unfold Nat.ModEq at H
      norm_num at H

      obtain ⟨n_pos, hn⟩ := hn

      have hn_geq_4 : 4≤n := by
        by_contra!
        interval_cases n
        all_goals (
          norm_num at hn
          rw [hn] at hp
          trivial
        )

      have h_n : ∃k : ℕ, n = 5 * k + 4 := by
        use (n-4)/5
        refine Nat.eq_add_of_sub_eq ?_ ?_
        exact hn_geq_4
        refine Eq.symm (Nat.mul_div_cancel' ?_)
        refine (Nat.modEq_iff_dvd' ?_).mp (id (Eq.symm H))
        exact hn_geq_4

      obtain ⟨k, hk⟩ := h_n

      rw [hk] at hn

      have : ((5 * k + 4) ^ 2/5 : ℚ) = 5*k^2 + 8*k + 16/5 := by ring
      push_cast at hn
      rw [this] at hn

      have : ⌊(5*k^2 + 8*k + 16/5 : ℚ)⌋ = 5*k^2 + 8*k + 3 := by
        apply Int.floor_eq_iff.mpr
        constructor
        · norm_num
        · norm_cast
          have : 5 * k ^ 2 + 8 * k + 3 + 1 = 5 * k ^ 2 + 8 * k + 4 := by ring
          rw [this]
          norm_num

      rw [this] at hn

      have : (5*k^2 + 8*k + 3 : ℤ) = (5*k+3)*(k+1) := by ring
      rw [this] at hn
      norm_cast at hn

      by_cases h: k=0
      · rw [h] at hn
        omega
      · have hn_prime: ¬ Nat.Prime p := by
          rw [hn]

          refine Nat.not_prime_mul ?_ ?_
          exact Ne.symm (Nat.ne_of_beq_eq_false rfl)
          exact Ne.symm ((fun {m n} ↦ Nat.succ_ne_succ.mpr) fun a ↦ h (id (Eq.symm a)))

        contradiction
  -- ha p ∈ {5,3,7} akkor létezik olyan n, amire teljesül az egyenlet
  · intro h
    rcases h with (rfl|rfl|rfl)
    · use 5
      norm_num
    · use 4
      norm_num
    · use 6
      norm_num
