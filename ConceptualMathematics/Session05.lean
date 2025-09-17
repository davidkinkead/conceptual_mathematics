import VersoManual
import ConceptualMathematics.Meta.Lean
import ConceptualMathematics.Article1
import ConceptualMathematics.Session03
import ConceptualMathematics.Article2
import ConceptualMathematics.Session04
import Mathlib

open Verso.Genre Manual InlineLean
open ConceptualMathematics
open CategoryTheory


#doc (Manual) "Session 5: Division of maps: Sections and retractions" =>

```savedImport
import ConceptualMathematics.Article1
import ConceptualMathematics.Session03
import ConceptualMathematics.Article2
import ConceptualMathematics.Session04
import Mathlib
open CategoryTheory
```

```savedLean (show := false)
namespace CM
local notation:80 g " ⊚ " f:80 => CategoryStruct.comp f g
```

:::question (questionTitle := "Exercise 1") (questionPage := "70")
(a) Show that if there is a map $`g` for which $`{h = g \circ f}`, then for any pair $`a_1`, $`a_2` of points $`{\mathbf{1} \rightarrow A}` of the domain $`A` of $`f` (and of $`h`) we have:
$$`\text{if}\; fa_1 = fa_2 \;\text{then}\; ha_1 = ha_2.`
(So, if for some pair of points one has $`{f a_1 = f a_2}` but $`{h a_1 \ne h a_2}`, then $`h` is not determined by $`f`.)

(b) Does the converse hold? That is, if maps (of sets) $`f` and $`h` satisfy the conditions above ('for any pair ... then $`{h a_1 = h a_2}`'), must there be a map $`{B \xrightarrow{g} C}` with $`{h = g \circ f}`?
:::

:::solution (solutionTo := "Exercise 1")
```savedComment
Exercise 5.1 (p. 70)
```

We use types instead of sets here, and we begin by showing that part (a) holds.

```savedLean
example {A B C : Type} {f : A ⟶ B} {h : A ⟶ C}
    (hg : ∃ g : B ⟶ C, h = g ⊚ f)
    : ∀ a₁ a₂ : Point A, f ⊚ a₁ = f ⊚ a₂ → h ⊚ a₁ = h ⊚ a₂ := by
  obtain ⟨g, hg⟩ := hg
  intro _ _ hfa
  rw [hg]
  repeat rw [← Category.assoc]
  rw [hfa]
```

For part (b), we first prove the converse in the case when $`f` is surjective.

```savedLean
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
```

Proof in the general case is slightly more complicated and is given below.

```savedLean
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
```
:::

:::definition (definitionTerm := "Constant map") (definitionPage := "71")
A map that can be factored through $`\mathbf{1}` is called a _constant map_.
:::

We implement `IsConstantMap` in Lean as follows:

```savedComment
IsConstantMap
```

```savedLean
def IsConstantMap {A C : Type} (h : A ⟶ C) :=
  ∃ (f : A ⟶ One) (g : One ⟶ C), h = g ⊚ f
```

:::question (questionTitle := "Exercise 2") (questionPage := "71")
(a) Show that if there is an $`f` with $`{g \circ f = h}`, then $`h` and $`g` satisfy: For any $`a` in $`A` there is at least one $`b` in $`B` for which $`{h(a) = g(b)}`.

(b) Does the converse hold? That is, if $`h` and $`g` satisfy the condition above, must there be a map $`f` with $`{h = g \circ f}`?
:::

:::solution (solutionTo := "Exercise 2")
```savedComment
Exercise 5.2 (p. 71)
```

We show that part (a) holds.

```savedLean
example {A B C : Type} {g : B ⟶ C} {h : A ⟶ C}
    (hf : ∃ f : A ⟶ B, g ⊚ f = h)
    : ∀ a : A, ∃ b : B, h a = g b := by
  intro a
  obtain ⟨f, hf⟩ := hf
  use f a
  rw [← hf]
  rfl
```

We show that the converse holds in part (b).

```savedLean
example {A B C : Type} {g : B ⟶ C} {h : A ⟶ C}
    (H : ∀ a : A, ∃ b : B, h a = g b)
    : ∃ f : A ⟶ B, g ⊚ f = h := by
  choose f_fun h_spec using H
  use f_fun
  funext a
  exact (h_spec a).symm
```
:::

:::definition (definitionTerm := "Section") (definitionPage := "72")
$`{A \xrightarrow{f} B}` is a _section of_ $`{B \xrightarrow{g} A}` if $`{g \circ f = 1_A}`.
:::

See the original presentation of this definition of section in Article II.

:::question (questionTitle := "Exercise 3") (questionPage := "75")
Draw the internal diagrams of all the sections of $`f`.
:::

:::solution (solutionTo := "Exercise 3")
```savedComment
Exercise 5.3 (p. 75)
```

```savedLean (show := false)
namespace Ex5_3
```

We label the elements in the first column of $`A` as $`a_{11}`, $`a_{12}`, $`a_{13}`, $`a_{14}` and the elements in the second column of $`A` as $`a_{21}`, $`a_{22}`; we label the element in the first column of $`B` as $`b_1` and the element in the second column of $`B` as $`b_2`.

```savedLean
inductive A where
  | a₁₁ | a₁₂ | a₁₃ | a₁₄ | a₂₁ | a₂₂
  deriving Fintype

inductive B where
  | b₁ | b₂
  deriving Fintype

def f : A ⟶ B
  | A.a₁₁ => B.b₁
  | A.a₁₂ => B.b₁
  | A.a₁₃ => B.b₁
  | A.a₁₄ => B.b₁
  | A.a₂₁ => B.b₂
  | A.a₂₂ => B.b₂
```

Then the sections are

```savedLean
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
```
:::

```savedLean (show := false)
end Ex5_3
```

```savedLean (show := false)
end CM
```
