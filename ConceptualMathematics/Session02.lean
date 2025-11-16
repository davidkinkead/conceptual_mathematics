import VersoManual
import ConceptualMathematics.Meta.Lean
import ConceptualMathematics.Article1
import Mathlib

open Verso.Genre Manual InlineLean
open ConceptualMathematics
open CategoryTheory


#doc (Manual) "Session 2: Sets, maps, and composition" =>

%%%
htmlSplit := .never
number := false
%%%

```savedImport
import ConceptualMathematics.Article1
import Mathlib
open CategoryTheory
```

```savedLean -show
namespace CM
local notation:80 g " ⊚ " f:80 => CategoryStruct.comp f g
```

# 1. Review of Article I

:::excerpt (excerptPage := "23")
If we recall that a point of a set $`A` is a map from a singleton set $`\mathbf{1}` to $`A`, we see that there is a simple _test for equality of maps of sets_ $`{A \xrightarrow{f} B}` and $`{A \xrightarrow{g} B}`:
$$`\text{If for each \textit{point}}\; \mathbf{1} \xrightarrow{a} A, f \circ a = g \circ a, \;\text{then}\; f = g.`
:::

```savedComment
Equality of maps of sets (p. 23)
```

We generalise to types here.

```savedLean
example {A B : Type} {f g : A ⟶ B}
    : (∀ a : Point A, f ⊚ a = g ⊚ a) → f = g := by
  intro h
  ext a'
  exact congrFun (h (fun _ ↦ a')) ()
```

```savedLean -show
end CM
```
