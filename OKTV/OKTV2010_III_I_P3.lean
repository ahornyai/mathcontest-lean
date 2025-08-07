import Mathlib.Tactic
/-
OKTV 2010/2011, III. kategória, I. forduló, 3. feladat:

Keresse meg az összes olyan p prímszámot, melyhez léteznek olyan a, b, c egész számok,
hogy a^2 + b^2 + c^2 = p és (a^4 + b^4 + c^4) osztható p-vel
----------
Bizonyítsuk, hogy az egyetlen megoldás p=2 és p=3
-/
def SolutionSet : Finset ℤ := {2,3}

theorem oktv2010_iii_i_iii (p : ℤ) (hp_geq_0 : p ≥ 0) (hp : Prime p) : p ∈ SolutionSet ↔ ∃ a b c, (a ≥ 0 ∧ b ≥ 0 ∧ c ≥ 0 ∧ a^2+b^2+c^2=p ∧ p ∣ a^4 + b^4 + c^4) := by
  unfold SolutionSet

  constructor
  · intro h
    simp at h

    rcases h with h | h
    · rw [h]
      use 1,1,0
      norm_num
    · rw [h]
      use 1,1,1
      norm_num
  · intro h
    obtain ⟨a, b, c, ⟨ha_nonneg, hb_nonneg, hc_nonneg, h2, h3⟩⟩ := h

    wlog this: a ≥ b ∧ b ≥ c with hw
    · have hbca_add : b ^ 4 + c ^ 4 + a ^ 4 = a^4 + b^4+c^4 := by ring_nf
      have hcba_add : c ^ 4 + b ^ 4 + a ^ 4 = a^4 + b^4+c^4 := by ring_nf
      have hbac_add : b ^ 4 + a ^ 4 + c ^ 4 = a^4 + b^4+c^4 := by ring_nf
      have hcab_add : c ^ 4 + a ^ 4 + b ^ 4 = a^4 + b^4+c^4 := by ring_nf
      have hacb_add : a ^ 4 + c ^ 4 + b ^ 4 = a^4 + b^4+c^4 := by ring_nf

      rcases lt_trichotomy a b with hab | hab | hab
      · rcases lt_trichotomy b c with hbc | hbc | hbc
        · apply hw p hp_geq_0 hp c b a hc_nonneg hb_nonneg ha_nonneg
          · linarith
          · rw [hcba_add]
            exact h3
          · omega
        · apply hw p hp_geq_0 hp b c a hb_nonneg hc_nonneg ha_nonneg
          · linarith
          · rw [hbca_add]
            exact h3
          · omega
        · rcases lt_trichotomy a c with hac | hac | hac
          · apply hw p hp_geq_0 hp b c a hb_nonneg hc_nonneg ha_nonneg
            · linarith
            · rw [hbca_add]
              exact h3
            · omega
          · apply hw p hp_geq_0 hp b a c hb_nonneg ha_nonneg hc_nonneg
            · omega
            · rw [hbac_add]
              exact h3
            · omega
          · apply hw p hp_geq_0 hp b a c hb_nonneg ha_nonneg hc_nonneg
            · linarith
            · rw [hbac_add]
              exact h3
            · omega
      · rcases lt_trichotomy a c with hac | hac | hac
        · apply hw p hp_geq_0 hp c a b hc_nonneg ha_nonneg hb_nonneg
          · linarith
          · rw [hcab_add]
            exact h3
          · omega
        · apply hw p hp_geq_0 hp a b c ha_nonneg hb_nonneg hc_nonneg
          · linarith
          · exact h3
          · omega
        · apply hw p hp_geq_0 hp a b c ha_nonneg hb_nonneg hc_nonneg
          · linarith
          · exact h3
          · omega
      · rcases lt_trichotomy b c with hbc | hbc | hbc
        · rcases lt_trichotomy a c with hac | hac | hac
          · apply hw p hp_geq_0 hp c a b hc_nonneg ha_nonneg hb_nonneg
            · linarith
            · rw [hcab_add]
              exact h3
            · omega
          · apply hw p hp_geq_0 hp a c b ha_nonneg hc_nonneg hb_nonneg
            · linarith
            · rw [hacb_add]
              exact h3
            · omega
          · apply hw p hp_geq_0 hp a c b ha_nonneg hc_nonneg hb_nonneg
            · linarith
            · rw [hacb_add]
              exact h3
            · omega
        · apply hw p hp_geq_0 hp a b c ha_nonneg hb_nonneg hc_nonneg
          · exact h2
          · exact h3
          · omega
        · apply hw p hp_geq_0 hp a b c ha_nonneg hb_nonneg hc_nonneg
          · exact h2
          · exact h3
          · omega

    obtain ⟨ha_geq_b, hb_geq_c⟩ := this

    by_cases h1 : p > 3
    · have ha_pos : a > 0 := by
        by_contra!
        have ha_eq_0 : a = 0 := by linarith
        have hb_eq_0 : b = 0 := by linarith
        have hc_eq_0 : c = 0 := by linarith

        rw [ha_eq_0, hb_eq_0, hc_eq_0] at h2
        rw [← h2] at hp
        norm_num at hp

      have hb_pos : b > 0 := by
        by_contra!
        have hb_eq_0 : b = 0 := by linarith
        have hc_eq_0 : c = 0 := by linarith

        rw [hb_eq_0, hc_eq_0] at h2
        rw [← h2] at hp
        norm_num at hp

      have : p^2 - 2*p*a^2 + a^4 = b^4 + c^4 + 2*b^2*c^2 := by nlinarith

      have p_div_1 : p ∣ b^4 + c^4 + 2*b^2*c^2 - a^4 := by
        rw [← this]
        field_simp

        have : p ^ 2 - 2 * p * a ^ 2 = p*(p - 2*a^2) := by ring
        rw [this]
        exact Int.dvd_mul_right p (p - 2 * a ^ 2)

      have p_div_2 : p ∣ 2*((a^2 - b*c)*(a^2 + b*c)) := by
        have : 2*((a^2 - b*c)*(a^2 + b*c)) = a ^ 4 + b ^ 4 + c ^ 4 - (b^4 + c^4 + 2*b^2*c^2 - a^4) := by ring
        rw [this]

        exact Int.dvd_sub h3 p_div_1

      have : p ∣ 2 ∨ p ∣ (a^2 - b*c)*(a^2 + b*c) := by exact Prime.dvd_or_dvd hp p_div_2

      have p_nat : ∃ n : ℕ, p = n := ⟨Int.natAbs p, by rw [Int.natAbs_of_nonneg hp_geq_0]⟩
      obtain ⟨pn, hp_nat⟩ := p_nat

      rcases this with h | h
      · have : p ≤ 2 := by exact Int.le_of_dvd (by norm_num) h
        linarith
      · have h : (p : ℤ) ∣ a^2 - b*c ∨ (p : ℤ) ∣ a^2 + b*c := by exact Prime.dvd_or_dvd hp h

        rcases h with h | h
        · have : a ^ 2 - b * c ≥ 0 := by
            by_contra!
            have : a^2 < b*c := by linarith
            have h5 : a^2 ≥ b^2 := by exact (sq_le_sq₀ hb_nonneg ha_nonneg).mpr ha_geq_b

            have : b*b < b*c := by linarith
            have : b < c := by exact Int.lt_of_mul_lt_mul_left this hb_nonneg

            omega

          have hl : a^2 - b*c > 0 := by
            by_contra! hc
            have h4 : a^2 = b*c := by linarith
            have h5 : a^2 ≥ b^2 := by exact (sq_le_sq₀ hb_nonneg ha_nonneg).mpr ha_geq_b
            rw [h4] at h5

            have : c ≥ b := by
              refine Int.le_of_mul_le_mul_left ?_ hb_pos
              linarith

            have hc_eq_b : c=b := by exact Int.le_antisymm hb_geq_c this
            rw [hc_eq_b, ← pow_two] at h4
            rw [sq_eq_sq₀ ha_nonneg hb_nonneg] at h4
            rw [h4, hc_eq_b] at h2

            have hpn_eq_3_mul_b_sq: pn = 3*b^2 := by linarith

            have hb_ge_1 : b ≠ 1 := by
              by_contra! h'
              rw [h'] at hpn_eq_3_mul_b_sq
              omega

            have b_nat : ∃ n : ℕ, b = n := ⟨Int.natAbs b, by rw [Int.natAbs_of_nonneg hb_nonneg]⟩
            obtain ⟨bn, hb_nat⟩ := b_nat
            rw [hb_nat] at hpn_eq_3_mul_b_sq

            have hp : Nat.Prime (3*bn^2) := by
              refine Prime.nat_prime ?_
              rw [hp_nat] at hp

              have : Prime (3*bn^2 : ℤ) ↔ Prime (3*bn^2 : ℕ) := by
                constructor
                · intro h
                  refine Nat.Prime.prime ?_
                  rw [hpn_eq_3_mul_b_sq] at hp
                  exact Nat.prime_iff_prime_int.mpr hp
                · intro h
                  rw [← hpn_eq_3_mul_b_sq]
                  exact hp

              rw [hpn_eq_3_mul_b_sq, this] at hp
              exact hp

            have hp_contra : ¬ Nat.Prime (3*bn^2) := by
              refine Nat.not_prime_mul ?_ ?_
              norm_num
              linarith

            contradiction

          have hu : a ^ 2 - b * c ≥ p := by exact Int.le_of_dvd hl h
          rw [← h2] at hu

          have : 0 ≥ b^2 + c^2 + b*c := by linarith
          have : b^2 + c^2 + b*c > 0 := by
            refine Int.add_pos_of_pos_of_nonneg ?_ ?_
            · refine Int.add_pos_of_pos_of_nonneg ?_ ?_
              exact Lean.Omega.Int.pos_pow_of_pos b 2 hb_pos
              exact sq_nonneg c
            · exact Int.mul_nonneg hb_nonneg hc_nonneg

          omega
        · have hl : a^2 + b*c > 0 := by
            refine Int.add_pos_of_pos_of_nonneg ?_ ?_
            exact Lean.Omega.Int.pos_pow_of_pos a 2 ha_pos
            exact Int.mul_nonneg hb_nonneg hc_nonneg
          have : a^2 + b*c ≥ p := by exact Int.le_of_dvd hl h
          have hu : a^2 + b*c > p := by
            by_contra!
            have h4 : c^2 + b*(b-c) = 0 := by linarith
            have : b*(b-c) ≥ 0 := by
              refine Int.mul_nonneg hb_nonneg ?_
              exact Int.sub_nonneg_of_le hb_geq_c
            have : c^2 = 0 ∧ b*(b-c) = 0 := by exact (add_eq_zero_iff_of_nonneg (by exact sq_nonneg c) this).mp h4

            obtain ⟨h5, hb_eq_0⟩ := this

            have hc_eq_0 : c=0 := by exact pow_eq_zero h5
            simp [hc_eq_0] at hb_eq_0

            omega

          rw [← h2] at hu

          have : 0 > c^2 + (b^2 - b*c) := by linarith
          have : c^2 + (b^2 - b*c) ≥ 0 := by
            refine Int.add_nonneg ?_ ?_
            · exact sq_nonneg c
            · have : 0 ≤ b ^ 2 - b * c ↔ 0 ≤ b*(b-c) := by ring_nf
              rw [this]

              refine Int.mul_nonneg hb_nonneg ?_
              exact Int.sub_nonneg_of_le hb_geq_c

          omega
    · interval_cases p
      all_goals simp at *
