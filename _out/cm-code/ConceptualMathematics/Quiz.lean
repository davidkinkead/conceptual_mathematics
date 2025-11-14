import ConceptualMathematics.Article1
import ConceptualMathematics.Session02
import ConceptualMathematics.Session03
import ConceptualMathematics.Article2
import ConceptualMathematics.Session04
import ConceptualMathematics.Session05
import ConceptualMathematics.Session09
import Mathlib
open CategoryTheory
namespace CM
local notation:80 g " ⊚ " f:80 => CategoryStruct.comp f g

/-!
Problem Quiz.1 (p. 108)
-/
namespace Quiz_1

inductive A
  | a
  deriving Fintype

inductive B
  | b₁ | b₂
  deriving Fintype

def f : A ⟶ B
  | A.a => B.b₁

def r : B ⟶ A
  | B.b₁ => A.a
  | B.b₂ => A.a

example : IsRetraction f := by
  use r
  change r ⊚ f = 𝟙 A
  funext x
  fin_cases x
  dsimp [f, r]

example : ¬(IsSection f) := by
  by_contra h
  obtain ⟨s, hs⟩ := h
  have h_false := congrFun hs B.b₂
  cases h_false

end Quiz_1

/-!
Problem Quiz.2 (p. 108)
-/
namespace Quiz_2

variable {𝒞 : Type u} [Category.{v, u} 𝒞] {C D : 𝒞}
         (p : C ⟶ D) (q : D ⟶ C) (hpq : p ⊚ q ⊚ p = p)

example : IsIdempotent (p ⊚ q) := {
  idem := by
    calc (p ⊚ q) ⊚ p ⊚ q
      _ = ((p ⊚ q) ⊚ p) ⊚ q := by rw [Category.assoc]
      _ = (p ⊚ q ⊚ p) ⊚ q := by rw [← Category.assoc p]
      _ = p ⊚ q := by rw [hpq]
}

example : IsIdempotent (q ⊚ p) := {
  idem := by
    calc (q ⊚ p) ⊚ q ⊚ p
      _ = q ⊚ p ⊚ q ⊚ p := by rw [Category.assoc (q ⊚ p)]
      _ = q ⊚ p := by rw [hpq]
}

end Quiz_2

/-!
Problem Quiz_2* (p. 108)
-/
namespace «Quiz_2*»

variable {𝒞 : Type u} [Category.{v, u} 𝒞] {C D : 𝒞}
         (p : C ⟶ D) (q : D ⟶ C) (hpq : p ⊚ q ⊚ p = p)

example : ∃ q', p ⊚ q' ⊚ p = p ∧ q' ⊚ p ⊚ q' = q' := by
  use q ⊚ p ⊚ q -- q'
  constructor
  · rw [← Category.assoc p, ← Category.assoc, hpq, hpq]
  · rw [Category.assoc (q ⊚ p ⊚ q)]
    repeat rw [← Category.assoc p]
    rw [hpq]
    repeat rw [Category.assoc q]
    rw [← Category.assoc (q ⊚ p), hpq]

end «Quiz_2*»

/-!
Problem Quiz_1* (p. 108)
-/
namespace «Quiz_1*»

abbrev A := ℕ
abbrev B := ℝ

def f : A ⟶ B
  | 0 => 0
  | n + 1 => n + 1

noncomputable def r : B ⟶ A
  | r => ⌊abs r⌋₊

example : IsRetraction f := by
  use r
  change r ⊚ f = 𝟙 A
  funext x
  dsimp [f, r]
  induction x with
  | zero => rw [abs_zero, Nat.floor_zero]
  | succ n =>
      dsimp
      norm_cast
      rw [Nat.floor_natCast]

example : ¬(IsSection f) := by
  by_contra h
  obtain ⟨s, hs⟩ := h
  have h_false := congrFun hs 0.5
  cases hx : s 0.5 with
  | zero =>
      rw [types_comp_apply, hx] at h_false
      dsimp [f] at h_false
      norm_num at h_false
  | succ n =>
      rw [types_comp_apply, hx] at h_false
      dsimp [f] at h_false
      have h_ge_1 : (1 : B) ≤ n + 1 := by norm_num
      linarith

end «Quiz_1*»

end CM

