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
import Mathlib

open Verso.Genre Manual InlineLean
open ConceptualMathematics
open CategoryTheory


#doc (Manual) "Test 1" =>

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
import Mathlib
open CategoryTheory
```

```savedLean -show
namespace CM
local notation:80 g " ⊚ " f:80 => CategoryStruct.comp f g
```

:::question (questionTitle := "Problem 1") (questionPage := "119")
```savedComment
Problem Test 1.1 (p. 119)
```

```savedLean -show
namespace Test1_1
```

Throughout this problem

```savedLean
inductive A where
  | Mara | Aurelio | Andrea
  deriving Fintype
```

(a) Find an _invertible_ map $`{A \xrightarrow{f} A}`, different from the identity map $`1_A`.

(b) Find an _idempotent_ map $`{A \xrightarrow{e} A}`, different from the identity map $`1_A`.

(c) Find another set $`B` and two maps
$$`B \xrightarrow{s} A \xrightarrow{r} B`
for which $`{r \circ s = 1_B}` and $`{s \circ r = e}`. (In this part, $`e` is still the map you chose in part (b).)
:::

:::solution (solutionTo := "Problem 1")
For part (a), we give a map $`f`, and we show that $`f` is invertible.

```savedLean
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
    all_goals (
      funext x
      fin_cases x <;> dsimp [f, finv]
    )
}
```

For part (b), we give a map $`e`, and we show that $`e` is idempotent.

```savedLean
def e : A ⟶ A
  | A.Mara => A.Mara
  | A.Aurelio => A.Mara
  | A.Andrea => A.Mara

instance : IsIdempotent e := {
  idem := by
    funext x
    fin_cases x <;> dsimp [e]
}
```

For part (c), we give a set $`B` and maps $`r` and $`s`, and we show that they satisfy the required properties.

```savedLean
inductive B where
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
```

```savedLean -show
end Test1_1
```
:::

:::question (questionTitle := "Problem 2") (questionPage := "119")
$`\mathbb{R}` is the set of all real numbers, and $`{\mathbb{R} \xrightarrow{f} \mathbb{R}}` is the map given by the explicit formula $`{f(x) = 4x — 7}` for each input $`x`. Show that $`f` has an inverse map. To do this, give an explicit formula for the inverse map $`g`, and then show that

(a) $`{(g \circ f)(x) = x}` for each real number $`x`, and that

(b) $`{(f \circ g)(x) = x}` for each real number $`x`.
:::

:::solution (solutionTo := "Problem 2")
```savedComment
Problem Test 1.2 (p. 119)
```

Put $`{g(x) = \dfrac{x + 7}{4}}`; then we have

```savedLean
example (f : ℝ ⟶ ℝ) (hf : ∀ x : ℝ, f x = 4 * x - 7)
    : ∃ g, ∀ x : ℝ, (g ⊚ f) x = x ∧ (f ⊚ g) x = x := by
  use fun x ↦ (x + 7) / 4 -- g
  intro x
  dsimp [CategoryStruct.comp]
  constructor
  · -- proof of part (a)
    rw [hf x]
    ring
  · -- proof of part (b)
    rw [hf ((x + 7) / 4)]
    ring
```
:::

```savedLean -show
end CM
```
