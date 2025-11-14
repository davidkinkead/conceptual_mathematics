import VersoManual
import ConceptualMathematics.Meta.Lean
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

open Verso.Genre Manual InlineLean
open ConceptualMathematics
open CategoryTheory


#doc (Manual) "Session 14: Maps preserve positive properties" =>

%%%
htmlSplit := .never
number := false
%%%

```savedImport
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
```

```savedLean -show
namespace CM
local notation:80 g " ⊚ " f:80 => CategoryStruct.comp f g
```

For the exercises in this Session, we use the category `Type` instead of the category 𝑺 of sets, and we are told to assume that $`{f \circ \alpha = \beta \circ f}`. (We use `End X` and `End Y` here instead of `X ⟶ X` and  `Y ⟶ Y` to facilitate the use of exponents in Exercises 2 and 5.)

```savedLean -show
namespace Ex14_1_3
```

```savedLean
variable (X Y : Type) (α : End X) (β : End Y)
         (f : X ⟶ Y) (hf_comm : f ⊚ α = β ⊚ f)
```

:::question (questionTitle := "Exercise 1") (questionPage := "170")
Let $`x_1` and $`x_2` be two points of $`X` and define $`{y_1 = f(x_1)}` and $`{y_2 = f(x_2)}`. If
$$`{\alpha(x_1) = \alpha(x_2) \text{ in } X}`
(i.e. pushing the button $`\alpha` we arrive at the same state whether the initial state was $`x_1` or $`x_2`) then show that
$$`{\beta(y_1) = \beta(y_2) \text{ in } Y}`
(the 'same' statement with button $`\beta` on the machine $`Y^{↻\beta}` with regard to its two states $`y_1` and $`y_2`).
:::

:::solution (solutionTo := "Exercise 1")
```savedComment
Exercise 14.1 (p. 170)
```

The solution below faithfully follows the one provided in the book on p. 171.

```savedLean
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
```

An alternative and more efficient implementation could be as follows:

```savedLean
example (x₁ x₂ : X) (y₁ y₂ : Y)
    (hy₁ : y₁ = f x₁) (hy₂ : y₂ = f x₂) (hα : α x₁ = α x₂)
    : β y₁ = β y₂ := by
  rw [hy₁, hy₂]
  change (β ⊚ f) x₁ = (β ⊚ f) x₂
  rw [← hf_comm]
  change f (α x₁) = f (α x₂)
  rw [hα]
```
:::

:::question (questionTitle := "Exercise 2") (questionPage := "170")
If instead we know that
$$`{x_2 = \alpha^5(x_1) \text{ in } X}`
(i.e. that starting from state $`x_1`, five pushes of the button $`\alpha` will bring $`X` to the state $`x_2`), show that the 'same' statement is true of the states $`y_1` and $`y_2` in $`Y^{↻\beta}`; i.e.
$$`{y_2 = \beta^5}(y_1) \text{ in } Y`
:::

:::solution (solutionTo := "Exercise 2")
```savedComment
Exercise 14.2 (p. 170)
```

The solution below faithfully follows the one provided in the book on p. 172.

```savedLean
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
```

We can improve upon this solution from the book by first proving a lemma `pow_comm` (which we'll also need later in Exercise 5).

```savedLean
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
```

An alternative and more efficient implementation now follows:

```savedLean
example (x₁ x₂ : X) (y₁ y₂ : Y)
    (hy₁ : y₁ = f x₁) (hy₂ : y₂ = f x₂) (h : x₂ = (α ^ 5) x₁)
    : y₂ = (β ^ 5) y₁ := by
  have hf_pow_comm : f ⊚ (α ^ 5) = (β ^ 5) ⊚ f :=
    pow_comm f α β hf_comm 5
  rw [hy₁, hy₂, h]
  change (f ⊚ (α ^ 5)) x₁ = ((β ^ 5) ⊚ f) x₁
  rw [hf_pow_comm]
```
:::

:::question (questionTitle := "Exercise 3") (questionPage := "170")
If $`{\alpha(x) = x}` (i.e. $`x` is an 'equilibrium state' or 'fixed point' of $`\alpha`), then the 'same' is true of $`{y = f(x)}` in $`Y^{↻\beta}`.
:::

:::solution (solutionTo := "Exercise 3")
```savedComment
Exercise 14.3 (p. 170)
```

The solution below faithfully follows the one provided in the book on pp. 172–173.

```savedLean
example (x : X) (y : Y) (hy : y = f x) (h : α x = x) : β y = y := by
  calc β y
    _ = β (f x) := by rw [hy]
    _ = (β ⊚ f) x := rfl
    _ = (f ⊚ α) x := by rw [hf_comm]
    _ = f (α x) := rfl
    _ = f x := by rw [h]
    _ = y := by rw [hy]
```
:::

```savedLean -show
end Ex14_1_3
```

:::question (questionTitle := "Exercise 4") (questionPage := "171")
Give an example in which $`x` is not a fixed point of $`\alpha` but $`{y = f(x)}` is a fixed point of $`\beta`. This illustrates that although certain important properties are 'preserved' by $`f` they are not necessarily 'reflected'. Hint: The simplest conceivable example of $`Y^{↻\beta}` will do.
:::

:::solution (solutionTo := "Exercise 4")
```savedComment
Exercise 14.4 (p. 171)
```

```savedLean -show
namespace Ex14_4
```

The solution below faithfully follows the one provided in the book on p. 174.

```savedLean
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
```

In our example, `X.x₁` is not a fixed point of $`\alpha`, but its image `f X.x₁` is a fixed point of $`\beta`.

```savedLean
example : ¬(α X.x₁ = X.x₁) ∧ β (f X.x₁) = f X.x₁ := by
  constructor
  · decide
  · dsimp [β]
```

```savedLean -show
end Ex14_4
```
:::

:::question (questionTitle := "Exercise 5") (questionPage := "171")
Show that if $`{\alpha^4(x) = x}`, then the 'same' is true of $`{y = f(x)}`. (Same idea as Exercise 2.) But give an example where $`{\alpha^4(x) = x}` and $`{\alpha^2(x) \ne x}`, while $`{\beta^2(y) = y}` and $`{\beta(y) \ne y}`. This illustrates that while $`f` preserves the property of being in a small cycle, the size of the cycle may decrease.
:::

:::solution (solutionTo := "Exercise 5")
```savedComment
Exercise 14.5 (p. 171)
```

```savedLean -show
namespace Ex14_5
```

For the first part of the exercise, we show that $`{\alpha^4(x) = x}` implies $`{\beta^4(f(x)) = f(x)}`. To do so, we make use of the lemma `pow_comm` that we defined earlier in Exercise 2.

```savedLean
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
```

For the second part of the exercise, we give the following example that meets the required conditions:

```savedLean
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
```

```savedLean -show
end Ex14_5
```
:::

```savedLean -show
end CM
```
