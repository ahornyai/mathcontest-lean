import Mathlib.Tactic

/-
OKTV 2020/2021, III. kategória, I. forduló, 1. feladat:

Mely n ≥ 0 egészekre lesz 625^n + 4^(2n+1) prímszám?
-/
lemma a_pow_4_plus_4b_pow_4_fact {a b : ℕ} (h: a ≥ 2*b):
  a^4 + 4*b^4 = (a^2+2*a*b+2*b^2)*(a^2-2*a*b+2*b^2) := by
  have a_sq_geq_2ab : a*a ≥ 2*b*a := by exact Nat.mul_le_mul_right a h
  rw [← Nat.pow_two a] at a_sq_geq_2ab
  rw [Nat.mul_right_comm 2 b a] at a_sq_geq_2ab

  have x_nat : ∃ n : ℤ, a = n := ⟨Int.natAbs a, rfl⟩
  have y_nat : ∃ n : ℤ, b = n := ⟨Int.natAbs b, rfl⟩

  obtain ⟨ai, hx⟩ := x_nat
  obtain ⟨bi, hy⟩ := y_nat

  have : ai^4 + 4*bi^4 = (ai^2+2*ai*bi+2*bi^2)*(ai^2-2*ai*bi+2*bi^2) := by linarith
  simp [← hx, ← hy] at this
  norm_cast at this

lemma pow_five_ge_twice_pow_two (n : ℕ) (h : n ≥ 1) : 5^n ≥ 2 * 2^n := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    cases n with
    | zero => exact (Nat.not_succ_le_zero 0 h).elim
    | succ n =>
      cases n with
      | zero => decide
      | succ n =>
        have ih' := ih (n + 1) (Nat.lt_succ_self _)
        omega

theorem oktv_2020_i_i (n : ℕ) : n=0 ↔ ∃ p, Nat.Prime p ∧ p = 625^n + 4^(2*n+1) := by
  constructor
  · intro h
    rw[h]
    use 5
    norm_num
  · intro h
    by_cases h': n=0
    · exact h'
    · obtain ⟨p,⟨hp,h⟩⟩ := h
      have a_sq_geq_2b : 5^n ≥ 2*(2^n) := by
        apply pow_five_ge_twice_pow_two
        exact Nat.one_le_iff_ne_zero.mpr h'

      have : p = ((5^n)^2 + 2*5^n*2^n + 2*(2^n)^2) * ((5^n)^2 - 2*5^n*2^n + 2*(2^n)^2) := by
        calc
          _ = (625) ^ n + 4 ^ (2 * n + 1) := by rw[h];
          _ = (5^n)^4 + 4 ^ (2 * n + 1) := by rw[Nat.pow_right_comm]
          _ = (5^n)^4 + 4 ^ (2 * n)*4 := by rw[← Nat.pow_succ]
          _ = (5^n)^4 + 2 ^ (2*n*2)*4 := by rw[Nat.pow_mul' 2 (2 * n) 2]
          _ = (5^n)^4 + 4*2^(n*4) := by ring
          _ = (5^n)^4 + 4*(2^n)^4 := by rw[Nat.pow_mul]
          _ = ((5^n)^2 + 2*5^n*2^n + 2*(2^n)^2) * ((5^n)^2 - 2*5^n*2^n + 2*(2^n)^2) := a_pow_4_plus_4b_pow_4_fact a_sq_geq_2b

      have : ¬ Nat.Prime p := by
        rw [this]
        refine Nat.not_prime_mul ?_ ?_
        · have : (5 ^ n) ^ 2 + 2 * 5 ^ n * 2 ^ n + 2 * (2 ^ n) ^ 2 > 1 := by
            refine Nat.lt_add_left ((5 ^ n) ^ 2 + 2 * 5 ^ n * 2 ^ n) ?_
            refine Nat.one_lt_of_ne_zero_of_even ?_ ?_
            exact Ne.symm (NeZero.ne' (2 * (2 ^ n) ^ 2))
            exact even_two_mul ((2 ^ n) ^ 2)

          exact Ne.symm (Nat.ne_of_lt this)
        · have : (5 ^ n) ^ 2 - 2 * 5 ^ n * 2 ^ n + 2 * (2 ^ n) ^ 2 > 1 := by
            refine Nat.lt_add_left ((5 ^ n) ^ 2 - 2 * 5 ^ n * 2 ^ n) ?_
            refine Nat.one_lt_of_ne_zero_of_even ?_ ?_
            exact Ne.symm (NeZero.ne' (2 * (2 ^ n) ^ 2))
            exact even_two_mul ((2 ^ n) ^ 2)

          exact Ne.symm (Nat.ne_of_lt this)

      contradiction
