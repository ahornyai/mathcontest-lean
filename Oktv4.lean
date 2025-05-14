import Mathlib.Tactic

/-
OKTV 2014/2015. II. kategória döntő I. feladat:
Az x, y, z olyan pozitív egészek, amelyekre az
x(y + 1)/(x − 1)
y(z + 1)/(y - 1)
z(x + 1)/(z − 1)
hányadosok mindegyike pozitív egész szám. Mi az xyz szorzat lehetséges legnagyobb
értéke?

x > 1, y > 1, z > 1
fogalmazzuk át oszthatóságra
(x-1) ∣ x*(y+1)
(y-1) ∣ y*(z+1)
(z-1) ∣ z*(x+1)
-/

noncomputable abbrev max_xyz : ℕ := 693

--theorem oktv_2014_iii_i : IsGreatest { x : ℕ | IsGood x*y*z } max_xyz := by {
--}

def SatisfiesConstraints (x y z : ℕ) : Prop :=
  x > 1 ∧ y > 1 ∧ z > 1 ∧
  (x - 1) ∣ (x * (y + 1)) ∧
  (y - 1) ∣ (y * (z + 1)) ∧
  (z - 1) ∣ (z * (x + 1))

def SatisfiesEquivConstraints (x y z : ℕ) : Prop :=
  x > 1 ∧ y > 1 ∧ z > 1 ∧
  (x - 1) ∣ (y + 1) ∧
  (y - 1) ∣ (z + 1) ∧
  (z - 1) ∣ (x + 1)

/-- The solution is a triple of positive integers satisfying our constraints -/
def Solution : Set (ℕ × ℕ × ℕ) :=
  {p | SatisfiesConstraints p.1 p.2.1 p.2.2}

/-- A predicate stating that p is the greatest element in the set S with respect to f -/
def IsGreatest2 {α β} [Preorder β] (S : Set α) (f : α → β) (p : α) : Prop :=
  p ∈ S ∧ ∀ q ∈ S, f q ≤ f p

/-- Product function for triples -/
def prod : ℕ × ℕ × ℕ → ℕ := λ p => p.1 * p.2.1 * p.2.2


theorem constraint_chain (x y z : ℕ) (h : SatisfiesEquivConstraints x y z) :
  x ≤ y + 2 ∧ y ≤ z + 2 ∧ z ≤ x + 2 := by
  rcases h with ⟨hx, hy, hz, hxy, hyz, hzx⟩
  sorry

/-- We prove that (9,7,11) gives the maximum possible product -/
theorem max_product_solution : IsGreatest2 Solution prod (7, 11, 9) := by
  unfold IsGreatest2 Solution prod
  constructor
  · simp [SatisfiesConstraints]
    norm_num
  · intro q hq
    simp [SatisfiesConstraints]
    unfold SatisfiesConstraints at hq
