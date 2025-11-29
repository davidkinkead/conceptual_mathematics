import ConceptualMathematics.Article2
import Mathlib
open CategoryTheory
namespace CM
local notation:80 g " ⊚ " f:80 => CategoryStruct.comp f g

/-!
Problem Test 1.1 (p. 119)
-/
namespace Test1_1

inductive A
  | Mara | Aurelio | Andrea
  deriving Fintype

def f : A ⟶ A
  | A.Mara => A.Aurelio
  | A.Aurelio => A.Andrea
  | A.Andrea => A.Mara

def finv : A ⟶ A
  | A.Mara => A.Andrea
  | A.Aurelio => A.Mara
  | A.Andrea => A.Aurelio

example : IsIso f := {
  out := by
    use finv
    constructor
    all_goals
      funext x
      fin_cases x <;> dsimp [f, finv]
}

def e : A ⟶ A
  | A.Mara => A.Mara
  | A.Aurelio => A.Mara
  | A.Andrea => A.Mara

instance : IsIdempotent e := {
  idem := by
    funext x
    fin_cases x <;> dsimp [e]
}

inductive B
  | b
  deriving Fintype

def r : A ⟶ B
  | A.Mara => B.b
  | A.Aurelio => B.b
  | A.Andrea => B.b

def s : B ⟶ A
  | B.b => A.Mara

example : r ⊚ s = 𝟙 B ∧ s ⊚ r = e := by
  constructor
  · show r ⊚ s = 𝟙 B
    rfl
  · show s ⊚ r = e
    funext x
    fin_cases x <;> rfl

end Test1_1

/-!
Problem Test 1.2 (p. 119)
-/
example (f : ℝ ⟶ ℝ) (hf : ∀ x : ℝ, f x = 4 * x - 7)
    : ∃ g, ∀ x : ℝ, (g ⊚ f) x = x ∧ (f ⊚ g) x = x := by
  use fun x ↦ (x + 7) / 4 -- g
  intro x
  dsimp [CategoryStruct.comp]
  constructor
  · -- Proof of part (a)
    rw [hf x]
    ring
  · -- Proof of part (b)
    rw [hf ((x + 7) / 4)]
    ring

end CM

