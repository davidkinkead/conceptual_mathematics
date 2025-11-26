import ConceptualMathematics.Article1
import Mathlib
open CategoryTheory
namespace CM
local notation:80 g " ⊚ " f:80 => CategoryStruct.comp f g

/-!
Exercise 5.1 (p. 70)
-/
example {A B C : Type} {f : A ⟶ B} {h : A ⟶ C}
    (hg : ∃ g : B ⟶ C, h = g ⊚ f)
    : ∀ a₁ a₂ : Point A, f ⊚ a₁ = f ⊚ a₂ → h ⊚ a₁ = h ⊚ a₂ := by
  obtain ⟨g, hg⟩ := hg
  intro _ _ hfa
  rw [hg]
  repeat rw [← Category.assoc]
  rw [hfa]

example {A B C : Type} {f : A ⟶ B} {h : A ⟶ C}
    (H : ∀ a₁ a₂ : Point A, f ⊚ a₁ = f ⊚ a₂ → h ⊚ a₁ = h ⊚ a₂)
    (hfsurj : Function.Surjective f)
    : ∃ g : B ⟶ C, h = g ⊚ f := by
  let g : B ⟶ C := fun β ↦ h (Classical.choose (hfsurj β))
  use g
  funext α
  let a₁ : Point A := fun _ ↦ α
  let a₂ : Point A := fun _ ↦ Classical.choose (hfsurj (f α))
  have hfa : f ⊚ a₁ = f ⊚ a₂ := by
    funext
    exact (Classical.choose_spec (hfsurj (f α))).symm
  have hha : h ⊚ a₁ = h ⊚ a₂ := H a₁ a₂ hfa
  apply congrFun hha ()

open Classical in
example {A B C : Type} [Nonempty C] {f : A ⟶ B} {h : A ⟶ C}
    (H : ∀ a₁ a₂ : Point A, f ⊚ a₁ = f ⊚ a₂ → h ⊚ a₁ = h ⊚ a₂)
    : ∃ g : B ⟶ C, h = g ⊚ f := by
  -- β : B may or may not be in the image of f,
  -- so we need to handle both cases
  let g : B ⟶ C := fun β ↦
    if β_in_image : ∃ α : A, f α = β then
      h (choose β_in_image)
    else
      choice inferInstance
  use g
  funext α
  let β_in_image_exists : ∃ α' : A, f α' = f α := ⟨α, rfl⟩
  let a₁ : Point A := fun _ ↦ α
  let a₂ : Point A := fun _ ↦ choose β_in_image_exists
  have hfa : f ⊚ a₁ = f ⊚ a₂ := by
    funext
    exact (choose_spec β_in_image_exists).symm
  have hha : h ⊚ a₁ = h ⊚ a₂ := H a₁ a₂ hfa
  have h_eq_h_chosen : h α = h (choose β_in_image_exists) :=
    congrFun hha ()
  have g_eq_h_chosen : g (f α) = h (choose β_in_image_exists) := by
    dsimp [g]
    rw [dif_pos β_in_image_exists]
  rw [types_comp_apply]
  rw [g_eq_h_chosen]
  exact h_eq_h_chosen

/-!
IsConstantMap
-/
def IsConstantMap {A C : Type} (h : A ⟶ C) :=
  ∃ (f : A ⟶ One) (g : One ⟶ C), h = g ⊚ f

/-!
Exercise 5.2 (p. 71)
-/
example {A B C : Type} {g : B ⟶ C} {h : A ⟶ C}
    (hf : ∃ f : A ⟶ B, g ⊚ f = h)
    : ∀ a : A, ∃ b : B, h a = g b := by
  intro a
  obtain ⟨f, hf⟩ := hf
  use f a
  rw [← hf]
  rfl

example {A B C : Type} {g : B ⟶ C} {h : A ⟶ C}
    (H : ∀ a : A, ∃ b : B, h a = g b)
    : ∃ f : A ⟶ B, g ⊚ f = h := by
  choose f_fun h_spec using H
  use f_fun
  funext a
  exact (h_spec a).symm

/-!
Exercise 5.3 (p. 75)
-/
namespace Ex5_3

inductive A
  | a₁₁ | a₁₂ | a₁₃ | a₁₄ | a₂₁ | a₂₂
  deriving Fintype

inductive B
  | b₁ | b₂
  deriving Fintype

def f : A ⟶ B
  | A.a₁₁ => B.b₁
  | A.a₁₂ => B.b₁
  | A.a₁₃ => B.b₁
  | A.a₁₄ => B.b₁
  | A.a₂₁ => B.b₂
  | A.a₂₂ => B.b₂

def s₁ : B ⟶ A
  | B.b₁ => A.a₁₁
  | B.b₂ => A.a₂₁

example : f ⊚ s₁ = 𝟙 B := by funext x; fin_cases x <;> rfl

def s₂ : B ⟶ A
  | B.b₁ => A.a₁₂
  | B.b₂ => A.a₂₁

example : f ⊚ s₂ = 𝟙 B := by funext x; fin_cases x <;> rfl

def s₃ : B ⟶ A
  | B.b₁ => A.a₁₃
  | B.b₂ => A.a₂₁

example : f ⊚ s₃ = 𝟙 B := by funext x; fin_cases x <;> rfl

def s₄ : B ⟶ A
  | B.b₁ => A.a₁₄
  | B.b₂ => A.a₂₁

example : f ⊚ s₄ = 𝟙 B := by funext x; fin_cases x <;> rfl

def s₅ : B ⟶ A
  | B.b₁ => A.a₁₁
  | B.b₂ => A.a₂₂

example : f ⊚ s₅ = 𝟙 B := by funext x; fin_cases x <;> rfl

def s₆ : B ⟶ A
  | B.b₁ => A.a₁₂
  | B.b₂ => A.a₂₂

example : f ⊚ s₆ = 𝟙 B := by funext x; fin_cases x <;> rfl

def s₇ : B ⟶ A
  | B.b₁ => A.a₁₃
  | B.b₂ => A.a₂₂

example : f ⊚ s₇ = 𝟙 B := by funext x; fin_cases x <;> rfl

def s₈ : B ⟶ A
  | B.b₁ => A.a₁₄
  | B.b₂ => A.a₂₂

example : f ⊚ s₈ = 𝟙 B := by funext x; fin_cases x <;> rfl

end Ex5_3

end CM

