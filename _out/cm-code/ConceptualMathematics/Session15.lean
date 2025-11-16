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
import ConceptualMathematics.Session14
import Mathlib
open CategoryTheory
namespace CM
local notation:80 g " ⊚ " f:80 => CategoryStruct.comp f g

/-!
Period of an element (p. 176)
-/
theorem period_four_of_period_one {Y : Type} (β : End Y) (y : Y)
    : β y = y → (β ^ 4) y = y := by
  intro hβ
  nth_rw 2 [← hβ, ← hβ, ← hβ, ← hβ]
  rfl

theorem period_four_of_period_two {Y : Type} (β : End Y) (y : Y)
    : (β ^ 2) y = y → (β ^ 4) y = y := by
  intro hβ2
  nth_rw 2 [← hβ2, ← hβ2]
  rfl

/-!
Exercise 15.1 (p. 177)
-/
open Function
example {X : Type} (α : End X) (x : X)
    : (α ^ 5) x = x ∧ (α ^ 7) x = x → α x = x := by
  rintro ⟨h5, h7⟩
  change α^[5] x = x at h5
  change α^[7] x = x at h7
  nth_rw 1 [← h5, ← h5, ← h5, ← h5, ← iterate_one α]
  nth_rw 2 [← h7, ← h7, ← h7]
  repeat rw [← iterate_add_apply α 5 _ x]
  rw [← iterate_add_apply α 1 20 x]
  repeat rw [← iterate_add_apply α 7 _ x]

/-!
Successor map (p. 178)
-/
def σ : ℕ ⟶ ℕ := (· + 1)

def ℕσ : SetWithEndomap := {
  t := ℕ
  carrier := Set.univ
  toEnd := σ
  toEnd_mem := fun _ ↦ Set.mem_univ _
}

/-!
Exercise 15.2 (p. 178)
-/
namespace Ex15_2

def ς : Fin 4 ⟶ Fin 4 := (· + 1)

def C₄ : SetWithEndomap := {
  t := Fin 4
  carrier := Set.univ
  toEnd := ς
  toEnd_mem := fun _ ↦ Set.mem_univ _
}

def f₀ : ℕσ.t ⟶ C₄.t
  | Nat.zero => (0 : Fin 4) -- f(0) = 0
  | n + 1 => ς (f₀ n)

def f₀' : ℕσ ⟶ C₄ := ⟨
  f₀,
  by
    constructor
    · exact fun _ _ ↦ Set.mem_univ _
    · funext x
      dsimp [f₀, ℕσ, C₄, σ, ς]
⟩

def f₁ : ℕσ.t ⟶ C₄.t
  | Nat.zero => (1 : Fin 4) -- f(0) = 1
  | n + 1 => ς (f₁ n)

def f₁' : ℕσ ⟶ C₄ := ⟨
  f₁,
  by
    constructor
    · exact fun _ _ ↦ Set.mem_univ _
    · funext x
      dsimp [f₁, ℕσ, C₄, σ, ς]
⟩

def f₂ : ℕσ.t ⟶ C₄.t
  | Nat.zero => (2 : Fin 4) -- f(0) = 2
  | n + 1 => ς (f₂ n)

def f₂' : ℕσ ⟶ C₄ := ⟨
  f₂,
  by
    constructor
    · exact fun _ _ ↦ Set.mem_univ _
    · funext x
      dsimp [f₂, ℕσ, C₄, σ, ς]
⟩

def f₃ : ℕσ.t ⟶ C₄.t
  | Nat.zero => (3 : Fin 4) -- f(0) = 3
  | n + 1 => ς (f₃ n)

def f₃' : ℕσ ⟶ C₄ := ⟨
  f₃,
  by
    constructor
    · exact fun _ _ ↦ Set.mem_univ _
    · funext x
      dsimp [f₃, ℕσ, C₄, σ, ς]
⟩

end Ex15_2

/-!
Exercise 15.3 (p. 179)
-/
/-!
Exercise 15.4 (p. 179)
-/
namespace Ex15_4

variable (X : Type) (α : X ⟶ X)

def Xα : SetWithEndomap := {
  t := X
  carrier := Set.univ
  toEnd := α
  toEnd_mem := fun _ ↦ Set.mem_univ _
}

example : α ⊚ (Xα X α).toEnd = (Xα X α).toEnd ⊚ α := rfl

end Ex15_4

/-!
Exercise 15.5 (p. 179)
-/
example (Yβ : SetWithEndomap) (f : ℕσ ⟶ Yβ) (y : Yβ.t)
    (hy : f.val (0 : ℕ) = y)
    : (f.val ⊚ σ) (0 : ℕ) = Yβ.toEnd y := by
  obtain ⟨f, _, hf_comm⟩ := f
  have h0 : ℕσ.toEnd (0 : ℕ) = (1 : ℕ) := rfl
  rw [← hy]
  dsimp [σ]
  rw [← types_comp_apply _ Yβ.toEnd, ← hf_comm, types_comp_apply, h0]

/-!
Exercise 15.6 (p. 181)
-/
namespace Ex15_6

inductive B
  | female | male

def β : B ⟶ B
  | B.female => B.female
  | B.male => B.female

inductive ParentType
  | isMother

structure Person where
  parentType : ParentType

def m : Person ⟶ Person := fun _ ↦ ⟨ParentType.isMother⟩

def Xm : SetWithEndomap := {
  t := Person
  carrier := Set.univ
  toEnd := m
  toEnd_mem := fun _ ↦ Set.mem_univ _
}

def g : Xm.t ⟶ B
  | ⟨ParentType.isMother⟩ => B.female

example : g ⊚ Xm.toEnd = β ⊚ g := rfl

def Bβ : SetWithEndomap := {
  t := B
  carrier := Set.univ
  toEnd := β
  toEnd_mem := fun _ ↦ Set.mem_univ _
}

def g' : Xm ⟶ Bβ := ⟨
  g,
  by
    constructor
    · exact fun _ _ ↦ Set.mem_univ _
    · rfl
⟩

end Ex15_6

/-!
Exercise 15.7 (p. 185)
-/
namespace Ex15_7

inductive X
  | a | a₁ | a₂ | a₃ | a₄ | b | c | d | d₁

-- Subscripts correspond to powers of α
-- (i.e., the number of applications of α to the element)
def α : X ⟶ X
  | X.a => X.a₁
  | X.a₁ => X.a₂
  | X.a₂ => X.a₃
  | X.a₃ => X.a₄
  | X.a₄ => X.a₂
  | X.b => X.a₂
  | X.c => X.a₃
  | X.d => X.d₁
  | X.d₁ => X.d

inductive Y
  | l | m | p | q | r | s | t | u | v | w | x | y | z

def β : Y ⟶ Y
  | Y.l => Y.m
  | Y.m => Y.l
  | Y.p => Y.r
  | Y.q => Y.r
  | Y.r => Y.t
  | Y.s => Y.t
  | Y.t => Y.v
  | Y.u => Y.s
  | Y.v => Y.u
  | Y.w => Y.x
  | Y.x => Y.y
  | Y.y => Y.w
  | Y.z => Y.y

def Xα : SetWithEndomap := {
  t := X
  carrier := Set.univ
  toEnd := α
  toEnd_mem := fun _ ↦ Set.mem_univ _
}

def Yβ : SetWithEndomap := {
  t := Y
  carrier := Set.univ
  toEnd := β
  toEnd_mem := fun _ ↦ Set.mem_univ _
}

def f₁ : Xα.t ⟶ Yβ.t
  | X.a => Y.w
  | X.a₁ => Y.x
  | X.a₂ => Y.y
  | X.a₃ => Y.w
  | X.a₄ => Y.x
  | X.b => Y.x
  | X.c => Y.y
  | X.d => Y.l
  | X.d₁ => Y.m

def f₁' : Xα ⟶ Yβ := ⟨
  f₁,
  by
    constructor
    · exact fun _ _ ↦ Set.mem_univ _
    · funext x
      cases x <;> rfl
⟩

def f₂ : Xα.t ⟶ Yβ.t
  | X.a => Y.w
  | X.a₁ => Y.x
  | X.a₂ => Y.y
  | X.a₃ => Y.w
  | X.a₄ => Y.x
  | X.b => Y.x
  | X.c => Y.y
  | X.d => Y.m
  | X.d₁ => Y.l

def f₂' : Xα ⟶ Yβ := ⟨
  f₂,
  by
    constructor
    · exact fun _ _ ↦ Set.mem_univ _
    · funext x
      cases x <;> rfl
⟩

def f₃ : Xα.t ⟶ Yβ.t
  | X.a => Y.w
  | X.a₁ => Y.x
  | X.a₂ => Y.y
  | X.a₃ => Y.w
  | X.a₄ => Y.x
  | X.b => Y.z
  | X.c => Y.y
  | X.d => Y.l
  | X.d₁ => Y.m

def f₃' : Xα ⟶ Yβ := ⟨
  f₃,
  by
    constructor
    · exact fun _ _ ↦ Set.mem_univ _
    · funext x
      cases x <;> rfl
⟩

def f₄ : Xα.t ⟶ Yβ.t
  | X.a => Y.w
  | X.a₁ => Y.x
  | X.a₂ => Y.y
  | X.a₃ => Y.w
  | X.a₄ => Y.x
  | X.b => Y.z
  | X.c => Y.y
  | X.d => Y.m
  | X.d₁ => Y.l

def f₄' : Xα ⟶ Yβ := ⟨
  f₄,
  by
    constructor
    · exact fun _ _ ↦ Set.mem_univ _
    · funext x
      cases x <;> rfl
⟩

def f₅ : Xα.t ⟶ Yβ.t
  | X.a => Y.x
  | X.a₁ => Y.y
  | X.a₂ => Y.w
  | X.a₃ => Y.x
  | X.a₄ => Y.y
  | X.b => Y.y
  | X.c => Y.w
  | X.d => Y.l
  | X.d₁ => Y.m

def f₅' : Xα ⟶ Yβ := ⟨
  f₅,
  by
    constructor
    · exact fun _ _ ↦ Set.mem_univ _
    · funext x
      cases x <;> rfl
⟩

def f₆ : Xα.t ⟶ Yβ.t
  | X.a => Y.x
  | X.a₁ => Y.y
  | X.a₂ => Y.w
  | X.a₃ => Y.x
  | X.a₄ => Y.y
  | X.b => Y.y
  | X.c => Y.w
  | X.d => Y.m
  | X.d₁ => Y.l

def f₆' : Xα ⟶ Yβ := ⟨
  f₆,
  by
    constructor
    · exact fun _ _ ↦ Set.mem_univ _
    · funext x
      cases x <;> rfl
⟩

def f₇ : Xα.t ⟶ Yβ.t
  | X.a => Y.y
  | X.a₁ => Y.w
  | X.a₂ => Y.x
  | X.a₃ => Y.y
  | X.a₄ => Y.w
  | X.b => Y.w
  | X.c => Y.x
  | X.d => Y.l
  | X.d₁ => Y.m

def f₇' : Xα ⟶ Yβ := ⟨
  f₇,
  by
    constructor
    · exact fun _ _ ↦ Set.mem_univ _
    · funext x
      cases x <;> rfl
⟩

def f₈ : Xα.t ⟶ Yβ.t
  | X.a => Y.y
  | X.a₁ => Y.w
  | X.a₂ => Y.x
  | X.a₃ => Y.y
  | X.a₄ => Y.w
  | X.b => Y.w
  | X.c => Y.x
  | X.d => Y.m
  | X.d₁ => Y.l

def f₈' : Xα ⟶ Yβ := ⟨
  f₈,
  by
    constructor
    · exact fun _ _ ↦ Set.mem_univ _
    · funext x
      cases x <;> rfl
⟩

def f₉ : Xα.t ⟶ Yβ.t
  | X.a => Y.y
  | X.a₁ => Y.w
  | X.a₂ => Y.x
  | X.a₃ => Y.y
  | X.a₄ => Y.w
  | X.b => Y.w
  | X.c => Y.z
  | X.d => Y.l
  | X.d₁ => Y.m

def f₉' : Xα ⟶ Yβ := ⟨
  f₉,
  by
    constructor
    · exact fun _ _ ↦ Set.mem_univ _
    · funext x
      cases x <;> rfl
⟩

def f₁₀ : Xα.t ⟶ Yβ.t
  | X.a => Y.y
  | X.a₁ => Y.w
  | X.a₂ => Y.x
  | X.a₃ => Y.y
  | X.a₄ => Y.w
  | X.b => Y.w
  | X.c => Y.z
  | X.d => Y.m
  | X.d₁ => Y.l

def f₁₀' : Xα ⟶ Yβ := ⟨
  f₁₀,
  by
    constructor
    · exact fun _ _ ↦ Set.mem_univ _
    · funext x
      cases x <;> rfl
⟩

def f₁₁ : Xα.t ⟶ Yβ.t
  | X.a => Y.z
  | X.a₁ => Y.y
  | X.a₂ => Y.w
  | X.a₃ => Y.x
  | X.a₄ => Y.y
  | X.b => Y.y
  | X.c => Y.w
  | X.d => Y.l
  | X.d₁ => Y.m

def f₁₁' : Xα ⟶ Yβ := ⟨
  f₁₁,
  by
    constructor
    · exact fun _ _ ↦ Set.mem_univ _
    · funext x
      cases x <;> rfl
⟩

def f₁₂ : Xα.t ⟶ Yβ.t
  | X.a => Y.z
  | X.a₁ => Y.y
  | X.a₂ => Y.w
  | X.a₃ => Y.x
  | X.a₄ => Y.y
  | X.b => Y.y
  | X.c => Y.w
  | X.d => Y.m
  | X.d₁ => Y.l

def f₁₂' : Xα ⟶ Yβ := ⟨
  f₁₂,
  by
    constructor
    · exact fun _ _ ↦ Set.mem_univ _
    · funext x
      cases x <;> rfl
⟩

end Ex15_7

/-!
Exercise 15.12 (p. 186)
-/
end CM

