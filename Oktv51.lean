import Mathlib.Tactic

/-
OKTV 2020/2021, III. kategória, I. forduló, 5. feladat

Határozzuk meg azokat az f, g : ℝ → ℝ függvényeket, amelyekre minden x ≠ y valós
szám esetén teljesül, hogy (f(x) - f(y))/(x-y) = g((x+y)/2))
-/
def SolutionSet : Set ((ℝ → ℝ) × (ℝ → ℝ)) := { ⟨f, g⟩ | ∃ a b c, ∀ x : ℝ, (f x = a*x^2 + b*x + c ∧ g x = 2*a*x + b) }

theorem oktv_2020_iii_v (f g : ℝ → ℝ) : ⟨f, g⟩ ∈ SolutionSet ↔ (∀ x y : ℝ, x ≠ y → (f x - f y)/(x-y) = g ((x+y)/2)) := by
  constructor
  · intro h x y hx_neq_y
    simp at h
    obtain ⟨a, b, c, h⟩ := h

    have hx_sub_y_neq_0 : x-y ≠ 0 := by exact sub_ne_zero_of_ne hx_neq_y

    have hfx : f x = a * x ^ 2 + b * x + c := by
      specialize h x

      exact h.left

    have hfy : f y = a * y ^ 2 + b * y + c := by
      specialize h y

      exact h.left

    have hg_eq : g ((x + y) / 2) = 2 * a * ((x + y) / 2) + b := by
      specialize h ((x+y)/2)

      exact h.right

    rw [hfx, hfy, hg_eq]

    field_simp
    ring
  · intro h

    have h₁ : ∀ x y, x ≠ y → (f x - f y) = (x - y) * g ((x + y) / 2) := by
      intro x₁ y₁ hx_neq_y

      specialize h x₁ y₁ hx_neq_y

      have : x₁ - y₁ ≠ 0 := by exact sub_ne_zero_of_ne hx_neq_y

      field_simp at h
      linarith

    have h₂ : ∀ x, f x = x * g (x/2) + f 0 := by
      intro x₁
      specialize h x₁ 0

      by_cases hx : x₁ = 0
      · rw [hx]
        linarith
      · have : (f x₁ - f 0) / (x₁ - 0) = g ((x₁ + 0) / 2) := by exact h hx

        field_simp at this
        linarith

    have h₃ : ∀ x y, x * g (x/2) - y * g (y/2) = (x - y) * g ((x + y) / 2) := by
      intro x₁ y₁

      by_cases hx_eq : x₁ = y₁
      · rw [hx_eq]
        norm_num
      · specialize h₁ x₁ y₁ hx_eq

        have : f x₁ = x₁ * g (x₁/2) + f 0 := by exact h₂ x₁
        rw [this] at h₁

        have : f y₁ = y₁ * g (y₁/2) + f 0 := by exact h₂ y₁
        rw [this] at h₁

        linarith

    let G : ℝ → ℝ := fun x ↦ g (x/2) - g 0

    have h₄ : ∀ x, g (x/2) = (G 1) * x + g 0 := by
      have hG_0_eq_0 : G 0 = 0 := by
        unfold G
        norm_num

      have h₅ : ∀ x y, x * G x - y * G y = (x - y) * G (x + y) := by
        intro x₁ y₁

        unfold G

        have : x₁ * (g (x₁ / 2) - g 0) - y₁ * (g (y₁ / 2) - g 0) = x₁ * g (x₁ / 2) - y₁ * g (y₁ / 2) - (x₁ - y₁) * g 0 := by ring
        rw [this]

        specialize h₃ x₁ y₁
        rw [h₃]

        ring

      have h₆ : ∀ x, -x * G (-x) - x * G (x) = 0 := by
        intro x₁

        by_cases hx_eq: x₁ = 0
        · rw [hx_eq]
          norm_num
        · specialize h₅ (-x₁) x₁
          rw [h₅]

          simp
          right
          exact hG_0_eq_0

      have h₇ : ∀ x y, x * G x + y * G (-y) = (x - y) * G (x + y) := by
        intro x₁ y₁
        specialize h₅ x₁ y₁

        have hyG_neg : y₁ * G y₁ = -y₁ * G (-y₁) := by
          specialize h₆ y₁
          linarith

        rw [hyG_neg] at h₅
        rw [← h₅]

        ring

      have h₈ : ∀ x y, (x - y) * G (x + y) = (x + y) * G (x - y) := by
        intro x₁ y₁
        specialize h₅ x₁ y₁
        specialize h₇ x₁ (-y₁)

        field_simp at h₇
        rw [show x₁ + -y₁ = x₁ - y₁ by ring] at h₇

        linarith

      have h₉ : ∀ x, G (2*x - 1) = G 1 * (2*x - 1) := by
        intro x₁
        specialize h₈ x₁ (1-x₁)
        field_simp at h₈

        rw [show x₁ - (1 - x₁) = 2*x₁ - 1 by ring] at h₈

        linarith

      intro x
      specialize h₉ ((x+1)/2)
      field_simp at h₉
      linarith

    use G 1, g 0, f 0
    intro x

    constructor
    · specialize h₂ x
      specialize h₄ x

      rw [h₄] at h₂
      rw [h₂]

      ring
    · specialize h₄ (2*x)

      rw [show 2 * x / 2 = x by ring] at h₄
      rw [h₄]

      ring
