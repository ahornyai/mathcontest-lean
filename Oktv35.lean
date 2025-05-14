import Mathlib.Tactic
/-
OKTV 2015/2016, II. kategória, I. forduló, 3. feladat:

A pozitív egész számok körében négy egymást követő páratlan szám négyzetének
az összegét vizsgáljuk. Hány ilyen számnégyes van 1 és 100 között, amelyeknél ez a
négyzetösszeg 36-tal osztható?
----
bizonyítsuk be, hogy 10 ilyen számnégyes van
n ∈ {8,10,17,19,26,28,35,37,44,46}
-/
theorem oktv_2015_ii_iii : ({n | 1 < n ∧ 2*n-3 < 100 ∧ 36 ∣ (2*n-3)^2 + (2*n-1)^2 + (2*n+1)^2 + (2*n+3)^2} : Set ℤ) = {8,10,17,19,26,28,35,37,44,46} := by
  refine Set.ext ?_
  intro x

  constructor
  · intro h

    obtain ⟨hx_gt_1, hx_lt_100, h⟩ := h

    have : 2*x-3 ≥ 0 := by linarith
    have : 2*x-1 ≥ 0 := by linarith

    have h1 : (2*x-3)^2 + (2*x-1)^2 + (2*x+1)^2 + (2*x+3)^2 = 4*(4*x^2+5) := by ring_nf

    have h2 : 9 ∣ 4*x^2 + 5 := by
      have h4_pos : (0 : ℤ) < 4 := by decide
      refine Int.dvd_of_mul_dvd ?_ h4_pos
      rw [h1] at h
      exact h

    have : 4*x^2 + 5 = 4*(x+1)*(x-1) + 9 := by ring_nf

    have x_nat : ∃ n : ℕ, x = n := ⟨Int.natAbs x, by rw [Int.natAbs_of_nonneg (by linarith)]⟩
    obtain ⟨xn, hxn⟩ := x_nat

    have xn_gt_1 : xn ≥ 1 := by linarith

    have h3 : 9 ∣ (xn+1)*(xn-1) := by
      rw [this] at h2

      have : 9 ∣ 4*((xn+1)*(xn-1)) := by
        rw [← mul_assoc]
        rw [hxn] at h2
        norm_cast at h2

        exact Nat.dvd_add_self_right.mp h2

      exact Nat.Coprime.dvd_of_dvd_mul_left (by decide) this

    have h4 : 9 ∣ x+1 ∨ 9 ∣ x-1 := by
      have : 3 ∣ x+1 ∨ 3∣x-1 := by
        rw [hxn]
        norm_cast
        refine (Nat.Prime.dvd_mul ?_).mp ?_
        exact Nat.prime_three

        have : 9=3*3 := by norm_num
        rw [this] at h3
        exact dvd_of_mul_right_dvd h3

      rcases this with h6 | h6
      · obtain ⟨k, hk⟩ := h6
        have : x = 3*k-1 := by omega

        have : (x+1)*(x-1) = 9*k^2-6*k := by
          rw [this]
          ring_nf

        have : 9 ∣ 9*k^2-6*k := by
          rw [← this]
          rw [hxn]
          norm_cast

        omega
      · obtain ⟨k, hk⟩ := h6
        have : x = 3*k+1 := by omega

        have : (x+1)*(x-1) = 9*k^2+6*k := by
          rw [this]
          ring_nf

        have : 9 ∣ 9*k^2+6*k := by
          rw [← this]
          rw [hxn]
          norm_cast

        omega

    rcases h4 with h5 | h5
    · obtain ⟨k, hk⟩ := h5
      have : x = 9*k-1 := by omega

      have k_lb : 0 < k := by omega
      have k_ub : k < 6 := by omega

      rw [this]

      interval_cases k
      all_goals decide
    · obtain ⟨k, hk⟩ := h5
      have : x = 9*k+1 := by omega

      have k_lb : 0 < k := by omega
      have k_ub : k < 6 := by omega

      rw [this]

      interval_cases k
      all_goals decide
  · intro h

    rcases h with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    all_goals decide
