import Mathlib.Tactic

/-
OKTV 2024/2025, I. kategória, II. forduló, 3. feladat:

Adott a pozitív egész számok halmazán értelmezett f függvény, melyre f (1) = 1, és tetszőleges n ≥ 2 esetén
f (n) = (n-1) * f(n-1) + (n-2) * f (n-2) + ... + 3*f(3) + 2*f(2) + 1*f(1)
Határozza meg az f(2025) értékét.
-/
theorem oktv2024_i_ii_iii  {f : ℕ → ℕ} (hf_1 : f 1 = 1)
  (hf : ∀ n ≥ 2, f n = ∑ x ∈ Finset.range (n-1), ((x+1) * f (x+1))) : f 2025 = Nat.factorial 2025 / 2 := by
  have h₁ : ∀ n ≥ 2, f n = Nat.factorial n / 2 := by
    intro n h
    let m := n - 2

    have hn : n = m + 2 := by exact (Nat.sub_eq_iff_eq_add h).mp rfl
    rw [hn]

    induction m with
    | zero => 
      simp
      rw [hf]

      norm_num
      exact hf_1
      norm_num
    | succ m ih =>
      rw [hf]

      rw [show m + 1 + 2 - 1 = m + 2 - 1 + 1 by rfl]
      rw [Finset.sum_range_succ]

      rw [show m + 2 - 1 + 1 = m + 2 by rfl]
      rw [ih]
      rw [hf] at ih
      rw [ih]

      rw [show m + 1 + 2 = m + 2 + 1 by rfl]
      nth_rewrite 3 [Nat.factorial_succ]
      ring_nf

      have h₂ : 2 ∣ (2 + m).factorial := by
        rw [show 2 + m = m + 1 + 1 by ring]
        repeat rw [Nat.factorial_succ]

        by_cases h_parity: Even m
        · obtain ⟨k, hk⟩ := h_parity
          rw [hk]
          ring_nf
          omega
        · have : Odd m := by exact Nat.not_even_iff_odd.mp h_parity
          obtain ⟨k, hk⟩ := this

          rw [hk]
          ring_nf
          omega

      obtain ⟨k, hk⟩ := h₂
      rw [hk, Nat.mul_div_right k (by norm_num)]

      apply Eq.symm (Nat.div_eq_of_eq_mul_right ?_ ?_)
      norm_num
      ring
      exact Nat.le_add_left 2 m
      exact Nat.le_add_left 2 (m + 1)

  rw [h₁]
  norm_num
