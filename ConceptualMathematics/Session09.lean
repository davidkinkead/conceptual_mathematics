import VersoManual
import ConceptualMathematics.Meta.Lean
import ConceptualMathematics.Article1
import ConceptualMathematics.Session03
import ConceptualMathematics.Article2
import ConceptualMathematics.Session04
import ConceptualMathematics.Session05
import Mathlib

open Verso.Genre Manual InlineLean
open ConceptualMathematics
open CategoryTheory


#doc (Manual) "Session 9: Retracts and idempotents" =>

```savedImport
import ConceptualMathematics.Article1
import ConceptualMathematics.Session03
import ConceptualMathematics.Article2
import ConceptualMathematics.Session04
import ConceptualMathematics.Session05
import Mathlib
open CategoryTheory
```

```savedLean (show := false)
namespace CM
local notation:80 g " ⊚ " f:80 => CategoryStruct.comp f g
```

:::question (questionTitle := "Exercise 1") (questionPage := "99")
(In the category of sets) Show that unless the set $`A` has a point and $`B` has none, then there is at least one map from $`A` to $`B`.
:::

:::solution (solutionTo := "Exercise 1")
```savedComment
Exercise 9.1 (p. 99)
```

TODO Exercise 9.1

  cases:
    A = ∅ => single map
    A ≠ ∅, B = ∅ => no map
    A ≠ ∅, B ≠ ∅ => at least one map
:::

:::definition (definitionTerm := "Retract") (definitionPage := "99")
$`A` is a _retract of_ $`B` means that there are maps $`{A \xrightarrow{s} B \xrightarrow{r} A}` with $`{r s = 1_A}`.
:::

The corresponding mathlib definition is `Retract`, which we print below for reference.

```lean
#print Retract
```

```
structure CategoryTheory.Retract.{v, u} {C : Type u} [Category.{v, u} C] (X Y : C) : Type v
number of parameters: 4
fields:
  CategoryTheory.Retract.i : X ⟶ Y
  CategoryTheory.Retract.r : Y ⟶ X
  CategoryTheory.Retract.retract : self.r ⊚ self.i = 𝟙 X := by
    cat_disch
constructor:
  CategoryTheory.Retract.mk.{v, u} {C : Type u} [Category.{v, u} C] {X Y : C} (i : X ⟶ Y) (r : Y ⟶ X)
    (retract : r ⊚ i = 𝟙 X := by cat_disch) : Retract X Y
```

:::question (questionTitle := "Exercise 2") (questionPage := "100")
(In any category) Show that

(R) $`A` is a retract of $`A`.

(T) If $`A` is a retract of $`B` and $`B` is a retract of $`C` then $`A` is a retract of $`C`.

Hint: You already proved (T) when you proved that if a composable pair of maps each has a retraction, then so does their composite.
:::

:::solution (solutionTo := "Exercise 2")
```savedComment
Exercise 9.2 (p. 100)
```

```savedLean (show := false)
namespace Ex9_2
```

```savedLean
variable {𝒞 : Type*} [Category 𝒞] {A B C : 𝒞}
```

We show that (R) holds.

```savedLean
example : Retract A A := {
  i := 𝟙 A
  r := 𝟙 A
}
```

We show that (T) holds (cf. Proposition 3 in Article II).

```savedLean
example (h₁ : Retract A B) (h₂ : Retract B C) : Retract A C := {
  i := h₂.i ⊚ h₁.i
  r := h₁.r ⊚ h₂.r
}
```

```savedLean (show := false)
end Ex9_2
```
:::

:::definition (definitionTerm := "Splitting") (definitionPage := "102")
(In any category) If $`{B \xrightarrow{e} B}` is an idempotent map, a _splitting of_ $`e` consists of an object $`A` together with two maps $`{A \xrightarrow{s} B \xrightarrow{r} A}` with $`{r s = 1_A}` and $`{s r = e}`.
:::

We implement `Splitting` in Lean as follows:

```savedComment
Splitting
```

```savedLean
structure Splitting {𝒞 : Type*} [Category 𝒞] {B : 𝒞}
    (e : B ⟶ B) [IsIdempotent e] where
  A : 𝒞
  s : A ⟶ B
  r : B ⟶ A
  rs : r ⊚ s = 𝟙 A
  sr : s ⊚ r = e
```

:::question (questionTitle := "Exercise 3") (questionPage := "102")
(In any category) Suppose that both $`{A \xrightarrow{s} B \xrightarrow{r} A}` and $`{A' \xrightarrow{s'} B \xrightarrow{r'} A'}` split the same idempotent $`{B \xrightarrow{e} B}`. Use these maps to construct an isomorphism $`{A \xrightarrow{f} A'}`.
:::

:::solution (solutionTo := "Exercise 3")
```savedComment
Exercise 9.3 (p. 102)
```

We construct an isomorphism $`f` as follows:

```savedLean
example {𝒞 : Type*} [Category 𝒞] {B : 𝒞}
    {e : B ⟶ B} [IsIdempotent e]
    (hsr : Splitting e) (hsr' : Splitting e)
    : Iso hsr.A hsr'.A := {
  hom := hsr'.r ⊚ hsr.s
  inv := hsr.r ⊚ hsr'.s
  hom_inv_id := by
    rw [Category.assoc, ← Category.assoc hsr'.r, hsr'.sr]
    -- rw [← hsr.sr] needs a bit of hand-holding here
    conv =>
      lhs
      arg 2
      arg 1
      rw [← hsr.sr]
    rw [Category.assoc, hsr.rs]
    rw [← Category.assoc, hsr.rs, Category.id_comp]
  inv_hom_id := by
    rw [Category.assoc, ← Category.assoc hsr.r, hsr.sr]
    -- rw [← hsr'.sr] likewise needs a bit of hand-holding here
    conv =>
      lhs
      arg 2
      arg 1
      rw [← hsr'.sr]
    rw [Category.assoc, hsr'.rs]
    rw [← Category.assoc, hsr'.rs, Category.id_comp]
}
```
:::

```savedLean (show := false)
end CM
```
