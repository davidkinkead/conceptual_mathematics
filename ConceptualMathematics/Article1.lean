import VersoManual
import ConceptualMathematics.Meta.Lean
import Mathlib

open Verso.Genre Manual InlineLean
open ConceptualMathematics
open CategoryTheory


#doc (Manual) "Article I: Sets, maps, composition" =>

```savedImport
import Mathlib
open CategoryTheory
```

```savedLean (show := false)
namespace CM
local notation:80 g " ⊚ " f:80 => CategoryStruct.comp f g
```

Until the introduction of the definition of _category_ at the end of Article I, we implement all _maps_ in the book as Lean _functions_.

:::question (questionTitle := "Exercise 1") (questionPage := "19")
Check to be sure you understand how we got diagrams (ii) and (iii) from the given diagram (i). Then fill in (iv) and (v) yourself, starting over from (i). Then check to see that (v) and (iii) are the same.
:::

:::solution (solutionTo := "Exercise 1")
```savedComment
Exercise I.1 (p. 19)
```

For simplicity, we use types here instead of sets. We number the elements in each set/type from top to bottom (top left to bottom right for $`D`).

```savedLean (show := false)
namespace ExI_1
```

```savedLean
inductive A where
  | a₁ | a₂ | a₃

inductive B where
  | b₁ | b₂ | b₃ | b₄

inductive C where
  | c₁ | c₂ | c₃ | c₄ | c₅

inductive D where
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
```

For diagram (iv), we have $`f` as above and $`{h \circ g}` as follows:

```savedLean
def hg : B → D
  | B.b₁ => D.d₁
  | B.b₂ => D.d₁
  | B.b₃ => D.d₃
  | B.b₄ => D.d₅

example : hg = h ∘ g := by
  funext x
  cases x <;> dsimp [g, h, hg]
```

For diagram (v), we have $`{(h \circ g) \circ f}` as follows, which is indeed the same as $`{h \circ (g \circ f)}` in diagram (iii):

```savedLean
def hgf : A → D
  | A.a₁ => D.d₁
  | A.a₂ => D.d₁
  | A.a₃ => D.d₃

example : hgf = (h ∘ g) ∘ f := by
  funext x
  cases x <;> dsimp [f, g, h, hgf]
```

```savedLean (show := false)
end ExI_1
```
:::

:::excerpt (excerptPage := "19")
One very useful sort of set is a 'singleton' set, a set with exactly one element.... Call this set '$`\mathbf{1}`'.
:::

We define $`\mathbf{1}` in Lean as the finite set containing the single element of type `Unit`.

```savedComment
CM_Finset.One
```

```savedLean
namespace CM_Finset

def One : Finset Unit := Finset.univ

end CM_Finset
```

:::definition (definitionTerm := "Point") (definitionPage := "19")
A _point_ of a set $`X` is a map $`{\mathbf{1} \rightarrow X}`.
:::

We define `Point` in Lean as a `Map` between `Finset`s. (The coercion allows a term inhabiting `Map` to be used directly as a function, so we can write `f`, `John`, and `eggs` below rather than `f.toFun`, `John.toFun`, and `eggs.toFun`.)

```savedComment
CM_Finset.Map, CM_Finset.Point
```

```savedLean
namespace CM_Finset

structure Map {α β : Type*} (X : Finset α) (Y : Finset β) where
  toFun : α → β
  maps_to_codomain : ∀ a : α, a ∈ X → toFun a ∈ Y

instance {α β : Type*} (X : Finset α) (Y : Finset β)
    : CoeFun (Map X Y) (fun _ ↦ α → β) where
  coe F := F.toFun

abbrev Point {β : Type*} (Y : Finset β) := Map One Y

end CM_Finset
```

:::excerpt (excerptPage := "19")
Since a point is a map, we can compose it with another map, and get a point again.
:::

We provide a Lean implementation below of the example given in the book on p. 19.

```savedLean
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
    all_goals (
      subst ha
      first | exact Or.inl rfl | exact Or.inr rfl
    )
}

def eggs : Point B := {
  toFun := fun _ ↦ "eggs"
  maps_to_codomain := by simp [B]
}

example : f ∘ John = eggs := rfl

end CM_Finset
```

:::htmlDetails (classDetails := "") (classSummary := "") (summary := "Replacing Finset with Set broadens the application to any set, not just finite sets.")
```savedComment
CM_Set.One, CM_Set.Map, CM_Set.Point
```

```savedLean
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
    all_goals (
      subst ha
      first | exact Or.inl rfl | exact Or.inr rfl
    )
}

def eggs : Point B := {
  toFun := fun _ ↦ "eggs"
  maps_to_codomain := by simp [B]
}

example : f ∘ John = eggs := rfl

end CM_Set
```
:::

:::htmlDetails (classDetails := "") (classSummary := "") (summary := "Using types instead of sets is cleaner and further broadens the application to any type, not just sets.")
```savedComment
One, CM_Type.Point
```

```savedLean
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
```
:::

We lift our definition for the _function_ `Point` between types to the _morphism_ `Point` in the category `Type` for later use. Note the application of `⟶` (`\hom`) for the morphism type instead of `→` (`\r`) for the function arrow.

```savedComment
Point
```

```savedLean
def Point (Y : Type) := One ⟶ Y
```

For Exercises 2–5 which follow, rather than providing exhaustive lists of maps, it seems more useful at this stage to introduce what the book calls _Alysia's formula_, even though that formula doesn't appear until slightly later (on pp. 33–34). The formula states that the number of different maps between two finite sets is equal to the number of elements in the codomain raised to the power of the number of elements in the domain — that is, the number of maps is $`{(\#\beta)^{(\#\alpha)}}`, where $`{\#\alpha}` is the size of the domain $`\alpha` and $`{\#\beta}` is the size of the codomain $`\beta`.

```savedComment
Alysia's formula
```

```savedLean
def Alysia's_formula (α β : Type*) [Fintype α] [Fintype β] : ℕ :=
  Fintype.card β ^ Fintype.card α
```

:::question (questionTitle := "Exercise 2") (questionPage := "20")
How many different maps $`f` are there with domain $`A` and codomain $`B`?
:::

:::solution (solutionTo := "Exercise 2")
```savedComment
Exercise I.2 (p. 20)
```

By Alysia's formula, we have $`{(\#B)^{(\#A)} = 2^3 = 8}` different maps.

```savedLean (name := outI_2)
open CM_Finset

#eval Alysia's_formula A B
```

```leanOutput outI_2
8
```
:::

:::question (questionTitle := "Exercise 3") (questionPage := "20")
Same, but for maps $`{A \xrightarrow{f} A}`?
:::

:::solution (solutionTo := "Exercise 3")
```savedComment
Exercise I.3 (p. 20)
```

By Alysia's formula, we have $`{(\#A)^{(\#A)} = 3^3 = 27}` different maps.

```savedLean (name := outI_3)
open CM_Finset

#eval Alysia's_formula A A
```

```leanOutput outI_3
27
```
:::

:::question (questionTitle := "Exercise 4") (questionPage := "20")
Same, but for maps $`{B \xrightarrow{f} A}`?
:::

:::solution (solutionTo := "Exercise 4")
```savedComment
Exercise I.4 (p. 20)
```

By Alysia's formula, we have $`{(\#A)^{(\#B)} = 3^2 = 9}` different maps.

```savedLean (name := outI_4)
open CM_Finset

#eval Alysia's_formula B A
```

```leanOutput outI_4
9
```
:::

:::question (questionTitle := "Exercise 5") (questionPage := "20")
Same, but for maps $`{B \xrightarrow{f} B}`?
:::

:::solution (solutionTo := "Exercise 5")
```savedComment
Exercise I.5 (p. 20)
```

By Alysia's formula, we have $`{(\#B)^{(\#B)} = 2^2 = 4}` different maps.

```savedLean (name := outI_5)
open CM_Finset

#eval Alysia's_formula B B
```

```leanOutput outI_5
4
```
:::

Exercises 6 and 7 concern idempotence, which the book formally introduces later on p. 54. For the purpose of these two exercises (and again aiming to avoid exhaustive lists of maps), we introduce the formula
$$`\sum_{k=0}^{n} {n \choose k} k^{n-k}`
for the total number of possible idempotents on a finite set. (See the Wikipedia article on [idempotence](https://en.wikipedia.org/wiki/Idempotence#Idempotent_functions) for additional information.)

```savedComment
idempotentCount
```

```savedLean
def idempotentCount (α : Type) [Fintype α] : ℕ :=
  let n := Fintype.card α
  ∑ k ∈ Finset.range (n + 1), (n.choose k) * k ^ (n - k)
```

:::question (questionTitle := "Exercise 6") (questionPage := "20")
How many maps $`{A \xrightarrow{f} A}` satisfy $`{f \circ f = f}`?
:::

:::solution (solutionTo := "Exercise 6")
```savedComment
Exercise I.6 (p. 20)
```

By the formula above, we have 10 different maps.

```savedLean (name := outI_6)
open CM_Finset

#eval idempotentCount A
```

```leanOutput outI_6
10
```
:::

:::question (questionTitle := "Exercise 7") (questionPage := "20")
How many maps $`{B \xrightarrow{g} B}` satisfy $`{g \circ g = g}`?
:::

:::solution (solutionTo := "Exercise 7")
```savedComment
Exercise I.7 (p. 20)
```

By the formula above, we have 3 different maps.

```savedLean (name := outI_7)
open CM_Finset

#eval idempotentCount B
```

```leanOutput outI_7
3
```
:::

:::question (questionTitle := "Exercise 8") (questionPage := "20")
Can you find a pair of maps $`{A \xrightarrow{f} B \xrightarrow{g} A}` for which $`{g \circ f = 1_A}`? If so, how many such pairs?
:::

:::solution (solutionTo := "Exercise 8")
```savedComment
Exercise I.8 (p. 20)
```

No such pair exists, since the image of $`1_A` has 3 elements, but the image of $`{g \circ f}` has only 2 elements.

```savedLean (show := false)
namespace ExI_8
```

```savedLean
open CM_Finset
```

We will begin using the Lean notation `𝟙 X`, for the identity morphism on $`X`, after we finish Article I and start working with morphisms and categories; for now, though, since we are still operating with functions and sets, we must define the identity map on $`A` explicitly.

```savedLean
def idA : Map A A := {
  toFun := id
  maps_to_codomain := by
    intro _ ha
    dsimp [A] at *
    repeat rw [Finset.mem_insert] at *
    rw [Finset.mem_singleton] at *
    rcases ha with ha | ha | ha
    all_goals (
      subst ha
      first
      | exact Or.inl rfl
      | exact Or.inr (Or.inl rfl)
      | exact Or.inr (Or.inr rfl)
    )
}

open Finset in
example : ¬(∃ f : Map A B, ∃ g : Map B A, g ∘ f = idA) := by
  -- Convert to the equivalent statement ∀ f g, g ∘ f ≠ idA.
  push_neg
  -- Assume that g ∘ f = idA for some f, g, and derive a contradiction.
  intro f g h_eq
  -- Since the functions g ∘ f and idA are equal, so are their images.
  have h_img_eq : (image g (image f A)).card = (image idA A).card := by
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
  -- while the image of idA(A) has 3 elements.
  have h_card_idA : (image idA A).card = 3 := rfl
  -- So we have a contradiction.
  rw [h_img_eq, h_card_idA] at h_card_gfA
  contradiction
```

```savedLean (show := false)
end ExI_8
```
:::

:::question (questionTitle := "Exercise 9") (questionPage := "20")
Can you find a pair of maps $`{B \xrightarrow{h} A \xrightarrow{k} B}` for which $`{k \circ h = 1_B}`? If so, how many such pairs?
:::

:::solution (solutionTo := "Exercise 9")
```savedComment
Exercise I.9 (p. 20)
```

We define one pair $`h`, $`k`.

```savedLean (show := false)
namespace ExI_9
```

```savedLean
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
    all_goals (
      subst hb
      first | exact Or.inl rfl | exact Or.inr (Or.inl rfl)
    )
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
    all_goals (
      subst ha
      first | exact Or.inl rfl | exact Or.inr rfl
    )
}
```

We define the identity map on $`B` explicitly (see the earlier comment under Exercise 8).

```savedLean
def idB : Map B B := {
  toFun
    | "eggs" => "eggs"
    | _ => "coffee"
  maps_to_codomain := by
    intro _ hb
    dsimp [B] at *
    rw [Finset.mem_insert, Finset.mem_singleton] at *
    rcases hb with hb | hb
    all_goals (
      subst hb
      first | exact Or.inl rfl | exact Or.inr rfl
    )
}
```

A proof that $`{k ∘ h = 1_B}` holds for our pair $`h`, $`k` is given below. (We define a macro for a repeated sequence of tactics to keep the proof concise.)

```savedLean
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
```

```savedLean (show := false)
end ExI_9
```

There are 12 such pairs: $`h(\mathit{eggs})` can take any one of three distinct values in $`A`, leaving $`h(\mathit{coffee})` to take one of the two remaining values, which together gives $`{3 \times 2 = 6}` combinations; and for each combination, $`k` can map the element in $`A` that is not in the image of $`h` to either $`\mathit{eggs}` or $`\mathit{coffee}`.
:::

:::definition (definitionTerm := "Category") (definitionPage := "21")
A _category_ consists of the DATA:

\(1\) OBJECTS

\(2\) MAPS

\(3\) For each map $`f`, one object as DOMAIN of $`f` and one object as CODOMAIN of $`f`

\(4\) For each object $`A` an IDENTITY MAP, which has domain $`A` and codomain $`A`

\(5\) For each pair of maps $`{A \xrightarrow{f} B \xrightarrow{g} C}`, a COMPOSITE MAP map $`{A \xrightarrow{g \;\mathrm{following}\; f} C}`

satisfying the following RULES:

\(i\) IDENTITY LAWS: If $`{A \xrightarrow{f} B}`, then $`{1_B \circ f = f}` and $`{f \circ 1_A = f}`

\(ii\) ASSOCIATIVE LAW: If $`{A \xrightarrow{f} B \xrightarrow{g} C \xrightarrow{h} D}`, then $`{(h \circ g) \circ f = h \circ (g \circ f)}`
:::

We print the mathlib definition of `Category` below for reference.

:::htmlDiv («class» := "print")
```lean
#print Category
```

```
class CategoryTheory.Category.{v, u} (obj : Type u) : Type (max u (v + 1))
number of parameters: 1
parents:
  CategoryTheory.Category.toCategoryStruct : CategoryStruct.{v, u} obj
fields:
  Quiver.Hom : obj → obj → Type v
  CategoryTheory.CategoryStruct.id : (X : obj) → X ⟶ X
  CategoryTheory.CategoryStruct.comp : {X Y Z : obj} → (X ⟶ Y) → (Y ⟶ Z) → (X ⟶ Z)
  CategoryTheory.Category.id_comp : ∀ {X Y : obj} (f : X ⟶ Y), f ⊚ 𝟙 X = f := by
    cat_disch
  CategoryTheory.Category.comp_id : ∀ {X Y : obj} (f : X ⟶ Y), 𝟙 Y ⊚ f = f := by
    cat_disch
  CategoryTheory.Category.assoc : ∀ {W X Y Z : obj} (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z), h ⊚ g ⊚ f = (h ⊚ g) ⊚ f := by
    cat_disch
constructor:
  CategoryTheory.Category.mk.{v, u} {obj : Type u} [toCategoryStruct : CategoryStruct.{v, u} obj]
    (id_comp : ∀ {X Y : obj} (f : X ⟶ Y), f ⊚ 𝟙 X = f := by cat_disch)
    (comp_id : ∀ {X Y : obj} (f : X ⟶ Y), 𝟙 Y ⊚ f = f := by cat_disch)
    (assoc : ∀ {W X Y Z : obj} (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z), h ⊚ g ⊚ f = (h ⊚ g) ⊚ f := by cat_disch) :
    Category.{v, u} obj
field notation resolution order:
  CategoryTheory.Category, CategoryTheory.CategoryStruct, Quiver
```
:::

```savedLean (show := false)
end CM
```
