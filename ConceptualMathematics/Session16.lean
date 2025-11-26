import VersoManual
import ConceptualMathematics.Meta.Lean
import Mathlib

open Verso.Genre Manual InlineLean
open ConceptualMathematics
open CategoryTheory


#doc (Manual) "Session 16: Idempotents, involutions, and graphs" =>

%%%
htmlSplit := .never
number := false
%%%

```savedImport
import Mathlib
open CategoryTheory
```

```savedLean -show
namespace CM
local notation:80 g " ⊚ " f:80 => CategoryStruct.comp f g
```

# 2. Solving exercises on maps of graphs

:::question (questionTitle := "Exercise 1") (questionPage := "195")
For a given object $`G` in a category 𝒞, the category 𝒞$`/G` has, as objects, objects of 𝒞 equipped with a given 𝒞-sorting $`{X \xrightarrow{s} G}` and, as maps, commutative triangles in 𝒞

...

For example, in Session 12, Exercise 3, a category modeling kinship relations was considered as 𝒞$`/G` where an object of 𝒞 = 𝑺↻↻ is thought of as a set of people equipped with _father_ and _mother_ endomaps and $`G` is the object of genders. On the other hand, in Exercise 17 of Article III, another description was given in terms of _two_ sets and four structural maps. Explain in what sense these two descriptions give the 'same' category.
:::

:::solution (solutionTo := "Exercise 1")
```savedComment
Exercise 16.1 (p. 195)
```

{htmlSpan (class := "todo")}[TODO Exercise 16.1]
:::

```savedLean -show
end CM
```
