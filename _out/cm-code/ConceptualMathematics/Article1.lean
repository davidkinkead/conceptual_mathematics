import Mathlib
open CategoryTheory
namespace CM
local notation:80 g " ⊚ " f:80 => CategoryStruct.comp f g

/-!
Exercise I.1 (p. 19)
-/
namespace ExI_1

inductive A
  | a₁ | a₂ | a₃

inductive B
  | b₁ | b₂ | b₃ | b₄

inductive C
  | c₁ | c₂ | c₃ | c₄ | c₅

inductive D
  | d₁ | d₂ | d₃ | d₄ | d₅ | d₆

def f : A → B
  | A.a₁ => B.b₁
  | A.a₂ => B.b₂
  | A.a₃ => B.b₃

def g : B → C
  | B.b₁ => C.c₂
  | B.b₂ => C.c₂
  | B.b₃ => C.c₄
  | B.b₄ => C.c₅

def h : C → D
  | C.c₁ => D.d₁
  | C.c₂ => D.d₁
  | C.c₃ => D.d₃
  | C.c₄ => D.d₃
  | C.c₅ => D.d₅

def hg : B → D
  | B.b₁ => D.d₁
  | B.b₂ => D.d₁
  | B.b₃ => D.d₃
  | B.b₄ => D.d₅

example : hg = h ∘ g := by
  funext x
  cases x <;> dsimp [g, h, hg]

def hgf : A → D
  | A.a₁ => D.d₁
  | A.a₂ => D.d₁
  | A.a₃ => D.d₃

example : hgf = (h ∘ g) ∘ f := by
  funext x
  cases x <;> dsimp [f, g, h, hgf]

end ExI_1

/-!
CM_Finset.One
-/
namespace CM_Finset

def One : Finset Unit := Finset.univ

end CM_Finset

/-!
CM_Finset.Map, CM_Finset.Point
-/
namespace CM_Finset

structure Map {α β : Type*} (X : Finset α) (Y : Finset β) where
  toFun : α → β
  maps_to_codomain : ∀ a : α, a ∈ X → toFun a ∈ Y

instance {α β : Type*} (X : Finset α) (Y : Finset β)
    : CoeFun (Map X Y) (fun _ ↦ α → β) where
  coe F := F.toFun

abbrev Point {β : Type*} (Y : Finset β) := Map One Y

end CM_Finset

namespace CM_Finset

def A : Finset String := { "John", "Mary", "Sam" }
def B : Finset String := { "eggs", "coffee" }

def John : Point A := {
  toFun := fun _ ↦ "John"
  maps_to_codomain := by simp [A]
}

def f : Map A B := {
  toFun
    | "John" => "eggs"
    | "Mary" => "eggs"
    | _ => "coffee"
  maps_to_codomain := by
    intro _ ha
    dsimp [A, B] at *
    repeat rw [Finset.mem_insert] at *
    rw [Finset.mem_singleton] at *
    rcases ha with ha | ha | ha
    all_goals
      subst ha
      first | exact Or.inl rfl | exact Or.inr rfl
}

def eggs : Point B := {
  toFun := fun _ ↦ "eggs"
  maps_to_codomain := by simp [B]
}

example : f ∘ John = eggs := rfl

end CM_Finset

/-!
CM_Set.One, CM_Set.Map, CM_Set.Point
-/
namespace CM_Set

def One : Set Unit := Set.univ

structure Map {α β : Type*} (X : Set α) (Y : Set β) where
  toFun : α → β
  maps_to_codomain : ∀ a : α, a ∈ X → toFun a ∈ Y

instance {α β : Type*} (X : Set α) (Y : Set β)
    : CoeFun (Map X Y) (fun _ ↦ α → β) where
  coe F := F.toFun

abbrev Point {β : Type*} (Y : Set β) := Map One Y

def A : Set String := { "John", "Mary", "Sam" }
def B : Set String := { "eggs", "coffee" }

def John : Point A := {
  toFun := fun _ ↦ "John"
  maps_to_codomain := by simp [A]
}

def f : Map A B := {
  toFun
    | "John" => "eggs"
    | "Mary" => "eggs"
    | _ => "coffee"
  maps_to_codomain := by
    intro _ ha
    dsimp [A, B] at *
    repeat rw [Set.mem_insert_iff] at *
    rw [Set.mem_singleton_iff] at *
    rcases ha with ha | ha | ha
    all_goals
      subst ha
      first | exact Or.inl rfl | exact Or.inr rfl
}

def eggs : Point B := {
  toFun := fun _ ↦ "eggs"
  maps_to_codomain := by simp [B]
}

example : f ∘ John = eggs := rfl

end CM_Set

/-!
One, CM_Type.Point
-/
def One := Unit

namespace CM_Type

def Point (Y : Type) := One → Y

def A := { a : String // a = "John" ∨ a = "Mary" ∨ a = "Sam" }
def B := { b : String // b = "eggs" ∨ b = "coffee" }

def John : Point A := fun _ ↦ ⟨"John", by simp⟩

def f : A → B := fun a ↦
  match a.val with
  | "John" => ⟨"eggs", by simp⟩
  | "Mary" => ⟨"eggs", by simp⟩
  | _ => ⟨"coffee", by simp⟩

def eggs : Point B := fun _ ↦ ⟨"eggs", by simp⟩

example : f ∘ John = eggs := rfl

end CM_Type

/-!
Point
-/
def Point (Y : Type) := One ⟶ Y

/-!
Alysia's formula
-/
def Alysia's_formula (α β : Type*) [Fintype α] [Fintype β] : ℕ :=
  Fintype.card β ^ Fintype.card α

/-!
Exercise I.2 (p. 20)
-/
open CM_Finset

#eval Alysia's_formula A B

/-!
Exercise I.3 (p. 20)
-/
open CM_Finset

#eval Alysia's_formula A A

/-!
Exercise I.4 (p. 20)
-/
open CM_Finset

#eval Alysia's_formula B A

/-!
Exercise I.5 (p. 20)
-/
open CM_Finset

#eval Alysia's_formula B B

/-!
idempotentCount
-/
def idempotentCount (α : Type) [Fintype α] : ℕ :=
  let n := Fintype.card α
  ∑ k ∈ Finset.range (n + 1), (n.choose k) * k ^ (n - k)

/-!
Exercise I.6 (p. 20)
-/
open CM_Finset

#eval idempotentCount A

/-!
Exercise I.7 (p. 20)
-/
open CM_Finset

#eval idempotentCount B

/-!
Exercise I.8 (p. 20)
-/
namespace ExI_8

open CM_Finset

def idA : Map A A := {
  toFun := id
  maps_to_codomain := by
    intro _ ha
    dsimp [A] at *
    repeat rw [Finset.mem_insert] at *
    rw [Finset.mem_singleton] at *
    rcases ha with ha | ha | ha
    all_goals
      subst ha
      first
      | exact Or.inl rfl
      | exact Or.inr (Or.inl rfl)
      | exact Or.inr (Or.inr rfl)
}

open Finset in
example : ¬(∃ f : Map A B, ∃ g : Map B A, g ∘ f = idA) := by
  -- Convert to the equivalent statement ∀ f g, g ∘ f ≠ idA
  push_neg
  -- Assume that g ∘ f = idA for some f, g, and derive a contradiction
  intro f g h_eq
  -- Since the functions g ∘ f and idA are equal, so are their images
  have h_img_eq
      : (image g (image f A)).card = (image idA A).card := by
    rw [image_image, h_eq]
  -- But the image of g(f(A)) has at most 2 elements,
  have h_card_gfA : (image g (image f A)).card ≤ 2 := by
    apply le_trans
    · exact card_image_le
    · change (image f A).card ≤ B.card
      apply card_le_card
      intro _ hfa
      rw [mem_image] at hfa
      obtain ⟨a, ha, rfl⟩ := hfa
      exact f.maps_to_codomain a ha
  -- while the image of idA(A) has 3 elements
  have h_card_idA : (image idA A).card = 3 := rfl
  -- So we have a contradiction
  rw [h_img_eq, h_card_idA] at h_card_gfA
  contradiction

end ExI_8

/-!
Exercise I.9 (p. 20)
-/
namespace ExI_9

open CM_Finset

def h : Map B A := {
  toFun
    | "eggs" => "John"
    | _ => "Mary"
  maps_to_codomain := by
    intro _ hb
    dsimp [A, B] at *
    repeat rw [Finset.mem_insert] at *
    rw [Finset.mem_singleton] at *
    rcases hb with hb | hb
    all_goals
      subst hb
      first | exact Or.inl rfl | exact Or.inr (Or.inl rfl)
}

def k : Map A B := {
  toFun
    | "John" => "eggs"
    | _ => "coffee"
  maps_to_codomain := by
    intro _ ha
    dsimp [A, B] at *
    repeat rw [Finset.mem_insert] at *
    rw [Finset.mem_singleton] at *
    rcases ha with ha | ha | ha
    all_goals
      subst ha
      first | exact Or.inl rfl | exact Or.inr rfl
}

def idB : Map B B := {
  toFun
    | "eggs" => "eggs"
    | _ => "coffee"
  maps_to_codomain := by
    intro _ hb
    dsimp [B] at *
    rw [Finset.mem_insert, Finset.mem_singleton] at *
    rcases hb with hb | hb
    all_goals
      subst hb
      first | exact Or.inl rfl | exact Or.inr rfl
}

syntax "eval_map" Lean.Parser.Tactic.rwRule : tactic

macro_rules
  | `(tactic| eval_map $fn_name) =>
    `(tactic| (
        rw [$fn_name]
        dsimp only [DFunLike.coe]
        split
        · contradiction
        · rfl
      )
    )

example : k ∘ h = idB := by
  funext x
  rw [Function.comp_apply]
  by_cases h_x_eggs : x = "eggs"
  · rw [h_x_eggs]
    have h_eval : h "eggs" = "John" := rfl
    have k_eval : k "John" = "eggs" := rfl
    have idB_eval : idB "eggs" = "eggs" := rfl
    rw [h_eval, k_eval, idB_eval]
  · have h_eval : h x = "Mary" := by eval_map h
    have k_eval : k "Mary" = "coffee" := by eval_map k
    have idB_eval : idB x = "coffee" := by eval_map idB
    rw [h_eval, k_eval, idB_eval]

end ExI_9

end CM

