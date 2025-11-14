import ConceptualMathematics.Article1
import ConceptualMathematics.Session02
import ConceptualMathematics.Session03
import ConceptualMathematics.Article2
import ConceptualMathematics.Session04
import ConceptualMathematics.Session05
import ConceptualMathematics.Session09
import ConceptualMathematics.Summary
import ConceptualMathematics.Review
import ConceptualMathematics.Session10
import ConceptualMathematics.Article3
import ConceptualMathematics.Session11
import ConceptualMathematics.Session12
import ConceptualMathematics.Session13
import Mathlib
open CategoryTheory
namespace CM
local notation:80 g " ⊚ " f:80 => CategoryStruct.comp f g

namespace Ex14_1_3

variable (X Y : Type) (α : End X) (β : End Y)
         (f : X ⟶ Y) (hf_comm : f ⊚ α = β ⊚ f)

/-!
Exercise 14.1 (p. 170)
-/
example (x₁ x₂ : X) (y₁ y₂ : Y)
    (hy₁ : y₁ = f x₁) (hy₂ : y₂ = f x₂) (hα : α x₁ = α x₂)
    : β y₁ = β y₂ := by
  have hβy₁ : β y₁ = f (α x₁) := by
    calc β y₁
      _ = β (f x₁) := by rw [hy₁]
      _ = (β ⊚ f) x₁ := rfl
      _ = (f ⊚ α) x₁ := by rw [hf_comm]
      _ = f (α x₁) := rfl
  have hβy₂ : β y₂ = f (α x₂) := by
    calc β y₂
      _ = β (f x₂) := by rw [hy₂]
      _ = (β ⊚ f) x₂ := rfl
      _ = (f ⊚ α) x₂:= by rw [hf_comm]
      _ = f (α x₂) := rfl
  have hfα : f (α x₁) = f (α x₂) := by rw [hα]
  rw [hβy₁, hβy₂, hfα]

example (x₁ x₂ : X) (y₁ y₂ : Y)
    (hy₁ : y₁ = f x₁) (hy₂ : y₂ = f x₂) (hα : α x₁ = α x₂)
    : β y₁ = β y₂ := by
  rw [hy₁, hy₂]
  change (β ⊚ f) x₁ = (β ⊚ f) x₂
  rw [← hf_comm]
  change f (α x₁) = f (α x₂)
  rw [hα]

/-!
Exercise 14.2 (p. 170)
-/
example (x₁ x₂ : X) (y₁ y₂ : Y)
    (hy₁ : y₁ = f x₁) (hy₂ : y₂ = f x₂) (h : x₂ = (α ^ 5) x₁)
    : y₂ = (β ^ 5) y₁ := by
  have hf_pow_comm : f ⊚ (α ^ 5) = (β ^ 5) ⊚ f := by
    calc f ⊚ (α ^ 5)
      _ = f ⊚ (α ⊚ α ^ 4) := rfl
      _ = (f ⊚ α) ⊚ (α ^ 4) := rfl
      _ = (β ⊚ f) ⊚ (α ^ 4) := by rw [hf_comm]
      _ = β ⊚ (f ⊚ (α ^ 4)) := rfl
      _ = β ⊚ ((f ⊚ α) ⊚ (α ^ 3)) := rfl
      _ = β ⊚ ((β ⊚ f) ⊚ (α ^ 3)) := by rw [hf_comm]
      _ = (β ⊚ (β ⊚ f)) ⊚ (α ^ 3) := rfl
      _ = ((β ^ 2) ⊚ f) ⊚ (α ^ 3) := rfl
      _ = (β ^ 2) ⊚ (f ⊚ (α ^ 3)) := rfl
      _ = (β ^ 2) ⊚ ((f ⊚ α) ⊚ (α ^ 2)) := rfl
      _ = (β ^ 2) ⊚ ((β ⊚ f) ⊚ (α ^ 2)) := by rw [hf_comm]
      _ = ((β ^ 2) ⊚ (β ⊚ f)) ⊚ (α ^ 2) := rfl
      _ = ((β ^ 3) ⊚ f) ⊚ (α ^ 2) := rfl
      _ = (β ^ 3) ⊚ (f ⊚ (α ^ 2)) := rfl
      _ = (β ^ 3) ⊚ ((f ⊚ α) ⊚ α) := rfl
      _ = (β ^ 3) ⊚ ((β ⊚ f) ⊚ α) := by rw [hf_comm]
      _ = ((β ^ 3) ⊚ (β ⊚ f)) ⊚ α := rfl
      _ = ((β ^ 4) ⊚ f) ⊚ α := rfl
      _ = (β ^ 4) ⊚ (f ⊚ α) := rfl
      _ = (β ^ 4) ⊚ (β ⊚ f) := by rw [hf_comm]
      _ = (β ^ 5) ⊚ f := rfl
  apply Eq.symm
  calc (β ^ 5) y₁
    _ = (β ^ 5) (f x₁) := by rw [hy₁]
    _ = ((β ^ 5) ⊚ f) x₁ := rfl
    _ = (f ⊚ (α ^ 5)) x₁ := by rw [hf_pow_comm]
    _ = f ((α ^ 5) x₁) := rfl
    _ = f x₂ := by rw [h]
    _ = y₂ := by rw [hy₂]

open Function
lemma _root_.pow_comm {X Y : Type} (f : X ⟶ Y)
    (α : End X) (β : End Y)
    (hf_comm : f ⊚ α = β ⊚ f) (n : ℕ)
    : f ⊚ (α^[n]) = (β^[n]) ⊚ f :=
  have hf_semiconj : Semiconj f α β :=
    semiconj_iff_comp_eq.mpr hf_comm
  have hf_pow_semiconj : Semiconj f (α^[n]) (β^[n]) :=
    Semiconj.iterate_right hf_semiconj n
  semiconj_iff_comp_eq.mp hf_pow_semiconj

example (x₁ x₂ : X) (y₁ y₂ : Y)
    (hy₁ : y₁ = f x₁) (hy₂ : y₂ = f x₂) (h : x₂ = (α ^ 5) x₁)
    : y₂ = (β ^ 5) y₁ := by
  have hf_pow_comm : f ⊚ (α ^ 5) = (β ^ 5) ⊚ f :=
    pow_comm f α β hf_comm 5
  rw [hy₁, hy₂, h]
  change (f ⊚ (α ^ 5)) x₁ = ((β ^ 5) ⊚ f) x₁
  rw [hf_pow_comm]

/-!
Exercise 14.3 (p. 170)
-/
example (x : X) (y : Y) (hy : y = f x) (h : α x = x) : β y = y := by
  calc β y
    _ = β (f x) := by rw [hy]
    _ = (β ⊚ f) x := rfl
    _ = (f ⊚ α) x := by rw [hf_comm]
    _ = f (α x) := rfl
    _ = f x := by rw [h]
    _ = y := by rw [hy]

end Ex14_1_3

/-!
Exercise 14.4 (p. 171)
-/
namespace Ex14_4

inductive X
  | x₁ | x₂
  deriving DecidableEq

inductive Y
  | y₁

def α : X ⟶ X
  | X.x₁ => X.x₂
  | X.x₂ => X.x₂

def β : Y ⟶ Y
  | Y.y₁ => Y.y₁

variable (f : X ⟶ Y) (hf_comm : f ⊚ α = β ⊚ f)

example : ¬(α X.x₁ = X.x₁) ∧ β (f X.x₁) = f X.x₁ := by
  constructor
  · decide
  · dsimp [β]

end Ex14_4

/-!
Exercise 14.5 (p. 171)
-/
namespace Ex14_5

example (X Y : Type) (α : End X) (β : End Y)
    (f : X ⟶ Y) (hf_comm : f ⊚ α = β ⊚ f)
    (x : X) (y : Y)
    (hy : y = f x) (h : (α ^ 4) x = x)
    : (β ^ 4) y = y := by
  have hf_pow_comm : f ⊚ (α ^ 4) = (β ^ 4) ⊚ f :=
    pow_comm f α β hf_comm 4
  rw [hy]
  nth_rw 2 [← h]
  apply Eq.symm
  change (f ⊚ (α ^ 4)) x = ((β ^ 4) ⊚ f) x
  rw [hf_pow_comm]

inductive X
  | x₁ | x₂ | x₃ | x₄

inductive Y
  | y₁ | y₂

def α : End X
  | X.x₁ => X.x₂
  | X.x₂ => X.x₃
  | X.x₃ => X.x₄
  | X.x₄ => X.x₁

def β : End Y
  | Y.y₁ => Y.y₂
  | Y.y₂ => Y.y₁

def f : X ⟶ Y
  | X.x₁ => Y.y₁
  | X.x₂ => Y.y₂
  | X.x₃ => Y.y₁
  | X.x₄ => Y.y₂

example (x : X) (y : Y) (hy : y = f x)
    : (α ^ 4) x = x ∧ ¬((α ^ 2) x = x)
      ∧
      (β ^ 2) y = y ∧ ¬(β y = y) := by
  and_intros
  · cases x <;> rfl
  · by_contra h
    change (α ⊚ α) x = x at h
    cases x
    all_goals (
      dsimp [α] at h
      contradiction
    )
  · cases y <;> rfl
  · by_contra h
    cases y
    all_goals (
      dsimp [β] at h
      contradiction
    )

end Ex14_5

end CM

