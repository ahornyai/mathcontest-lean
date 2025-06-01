import Mathlib.Tactic

/-
Arany Dániel 2011/2012 Haladók II. kategória II. forduló I. feladat

Mely x és y természetes számokra igaz, hogy √x + √y = √1000?
-/
def SolutionSet : Set (ℕ × ℕ) := {(0, 1000), (10, 810), (40, 640), (90, 490), (160, 360), (250, 250), (360, 160), (490, 90), (640, 40), (810, 10), (1000, 0)}

lemma add_mem_sq {x y : ℕ} (h : √(x : ℝ) + √(y : ℝ) = √(1000 : ℝ)) : IsSquare (10*x) := by
  have h1 : √(y : ℝ) = √1000 - √x := by exact Eq.symm (sub_eq_of_eq_add' (id (Eq.symm h)))
      
  rw [← sq_eq_sq₀, sub_pow_two] at h1
  repeat rw [Real.sq_sqrt] at h1
  rw [mul_assoc, ← Real.sqrt_mul] at h1

  have : √(1000*x : ℝ) = 10 * √(10*x) := by
    have : (1000*x : ℝ) = 10^2 * 10*x := by norm_num
    rw [this]
    simp
    rw [← mul_assoc]
  
  rw [this] at h1

  have : √(10*x : ℝ) = (x-y+1000)/20 := by linarith
  have : ∃a : ℚ, a=√(10*x : ℝ) := by
    use (x-y+1000)/20
    rw [this]
    simp
  
  obtain ⟨k, hk⟩ := this
  rw [← sq_eq_sq₀, Real.sq_sqrt] at hk
  norm_cast at hk

  refine Rat.isSquare_natCast_iff.mp ?_
  rw [← hk]
  exact IsSquare.sq k
  
  linarith
  rw [hk]; exact Real.sqrt_nonneg (10 * ↑x)
  exact Real.sqrt_nonneg (10 * ↑x)
  norm_num
  exact Nat.cast_nonneg' x
  exact Nat.ofNat_nonneg' 1000
  exact Nat.cast_nonneg' y
  exact Real.sqrt_nonneg ↑y
  have : √(y : ℝ) ≥ 0 := by exact Real.sqrt_nonneg ↑y
  linarith

lemma exists_nat_of_sq {x : ℕ} (h : IsSquare (10*x)) : ∃k : ℕ, x=10*k^2 := by
  obtain ⟨r, hr⟩ := h
  
  have : (∃k : ℕ, x=10*k^2) ↔ (∃k : ℕ, 10*x=(10*k)^2) := by
    refine exists_congr ?_
    intro a
    
    have : (10*a)^2 = 10*10*a^2 := by ring
    rw [this]
    
    omega
  
  rw [this, hr]
  use r/10

  have : 10 ∣ r*r := by exact Dvd.intro x hr
  have : 10 ∣ r := by sorry
  
  have : (10*(r/10)) = r := by exact Nat.mul_div_cancel' this
  
  rw [this]
  rw [Nat.pow_two]

theorem arany2012_advanced_ii_ii_i (x y : ℕ) : (√(x : ℝ) + √(y : ℝ) = √(1000 : ℝ)) ↔ ⟨x, y⟩ ∈ SolutionSet := by
  unfold SolutionSet
  simp

  constructor
  · intro h
    
    have hx_sq : IsSquare (10*x) := by exact add_mem_sq h
    have hy_sq : IsSquare (10*y) := by
      rw [add_comm] at h
      exact add_mem_sq h
    
    have : ∃k : ℕ, x=10*k^2 := by exact exists_nat_of_sq hx_sq
    obtain ⟨k, hx⟩ := this

    have : ∃n : ℕ, y=10*n^2 := by exact exists_nat_of_sq hy_sq
    obtain ⟨n, hy⟩ := this

    /- prove that k+n = 10 -/
    rw [hx, hy] at h
    push_cast at h

    repeat rw [Real.sqrt_mul (by norm_num)] at h
    
    have : √(1000 : ℝ) = 10 * √(10) := by
      have : (1000 : ℝ) = 10^2 * 10 := by norm_num
      rw [this]
      simp
    rw [this] at h
    field_simp at h
    
    have : √10 * k + √10 * n = (k+n) * √10 := by linarith
    rw [this, mul_left_inj' (by norm_num)] at h
    norm_cast at h

    have hk_leq_10 : k ≤ 10 := by linarith
    have hn_eq : n=10-k := by omega
    rw [hn_eq] at hy

    interval_cases k <;> omega
  · intro h
    have : 0 ≤ √(x : ℝ) + √(y : ℝ) := by
      refine add_nonneg ?_ ?_
      exact Real.sqrt_nonneg ↑x
      exact Real.sqrt_nonneg ↑y
    
    rw [← sq_eq_sq₀ this (by norm_num)]
    rw [add_pow_two]
    repeat rw [Real.sq_sqrt]
    rw [mul_assoc, ← Real.sqrt_mul]
    
    rcases h with h | h | h | h | h | h | h | h | h | h | h
    all_goals
      obtain ⟨rfl, rfl⟩ := h
      norm_num
    
    exact Nat.cast_nonneg' x
    exact Nat.ofNat_nonneg' 1000
    exact Nat.cast_nonneg' y
    exact Nat.cast_nonneg' x
