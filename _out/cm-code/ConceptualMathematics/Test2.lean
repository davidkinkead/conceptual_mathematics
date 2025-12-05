import ConceptualMathematics.Article3
import Mathlib
open CategoryTheory
namespace CM
local notation:80 g " ⊚ " f:80 => CategoryStruct.comp f g

/-!
Problem Test 2.1 (p. 204)
-/
example (X Y : SetWithEndomap) (f : X ⟶ Y) :
    (∃ x ∈ X.carrier, X.toEnd x = x) →
    (∃ y ∈ Y.carrier, Y.toEnd y = y) := by
  obtain ⟨f, hf_mtc, hf_comm⟩ := f
  intro ⟨x, hx, hα⟩
  use f x
  constructor
  · exact hf_mtc x hx
  · rw [← types_comp_apply _ Y.toEnd, ← hf_comm, types_comp_apply,
        hα]

/-!
Problem Test 2.2 (p. 204)
-/
namespace Test2_2

inductive A₁
  | a | b

inductive D₁
  | p | q | r

def G₁ : IrreflexiveGraph := {
  tA := A₁
  carrierA := Set.univ
  tD := D₁
  carrierD := Set.univ
  toSrc := fun
    | A₁.a => D₁.p
    | A₁.b => D₁.q
  toSrc_mem := fun _ ↦ Set.mem_univ _
  toTgt := fun
    | A₁.a => D₁.r
    | A₁.b => D₁.r
  toTgt_mem := fun _ ↦ Set.mem_univ _
}

inductive A₂
  | c | d

inductive D₂
  | v | w

def G₂ : IrreflexiveGraph := {
  tA := A₂
  carrierA := Set.univ
  tD := D₂
  carrierD := Set.univ
  toSrc := fun
    | A₂.c => D₂.w
    | A₂.d => D₂.v
  toSrc_mem := fun _ ↦ Set.mem_univ _
  toTgt := fun
    | A₂.c => D₂.w
    | A₂.d => D₂.w
  toTgt_mem := fun _ ↦ Set.mem_univ _
}

def f₁ : G₁ ⟶ G₂ := {
  val := (
    fun -- maps arrows
      | A₁.a => A₂.d
      | A₁.b => A₂.d,
    fun -- maps dots
      | D₁.p => D₂.v
      | D₁.q => D₂.v
      | D₁.r => D₂.w
  )
  property := by
    split_ands
    all_goals
      first | exact fun _ _ ↦ Set.mem_univ _
            | funext x; cases x <;> rfl
}

def f₂ : G₁ ⟶ G₂ := {
  val := (
    fun -- maps arrows
      | A₁.a => A₂.c
      | A₁.b => A₂.c,
    fun -- maps dots
      | D₁.p => D₂.w
      | D₁.q => D₂.w
      | D₁.r => D₂.w
  )
  property := by
    split_ands
    all_goals
      first | exact fun _ _ ↦ Set.mem_univ _
            | funext x; cases x <;> rfl
}

def f₃ : G₁ ⟶ G₂ := {
  val := (
    fun -- maps arrows
      | A₁.a => A₂.c
      | A₁.b => A₂.d,
    fun -- maps dots
      | D₁.p => D₂.w
      | D₁.q => D₂.v
      | D₁.r => D₂.w
  )
  property := by
    split_ands
    all_goals
      first | exact fun _ _ ↦ Set.mem_univ _
            | funext x; cases x <;> rfl
}

def f₄ : G₁ ⟶ G₂ := {
  val := (
    fun -- maps arrows
      | A₁.a => A₂.d
      | A₁.b => A₂.c,
    fun -- maps dots
      | D₁.p => D₂.v
      | D₁.q => D₂.w
      | D₁.r => D₂.w
  )
  property := by
    split_ands
    all_goals
      first | exact fun _ _ ↦ Set.mem_univ _
            | funext x; cases x <;> rfl
}

end Test2_2

/-!
Problem Test 2.3 (p. 204)
-/
namespace Test2_3

inductive X
  | x₁ | x₂ | x₃

def α : End X
  | X.x₁ => X.x₂
  | X.x₂ => X.x₃
  | X.x₃ => X.x₃

example : α ^ 2 = α ^ 3 ∧ α ≠ α ^ 2 := by
  constructor
  · funext x
    cases x <;> rfl
  · by_contra h
    have h_false : α X.x₁ = (α ^ 2) X.x₁ := congrFun h X.x₁
    have hα : α X.x₁ = X.x₂ := rfl
    have hαα : (α ^ 2) X.x₁ = X.x₃ := rfl
    rw [hα, hαα] at h_false
    contradiction

example : α ^ 2 = α ^ 3 ∧ α ≠ α ^ 2 := by
  constructor
  · funext x
    cases x <;> rfl
  · by_contra h
    have h_false : α X.x₁ = (α ^ 2) X.x₁ := congrFun h X.x₁
    -- have hα : α X.x₁ = X.x₂ := rfl
    -- have hαα : (α ^ 2) X.x₁ = X.x₃ := rfl
    -- rw [hα, hαα] at h_false
    contradiction

end Test2_3

end CM

