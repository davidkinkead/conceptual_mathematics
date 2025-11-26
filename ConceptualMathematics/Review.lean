import VersoManual
import ConceptualMathematics.Meta.Lean
import Mathlib

open Verso.Genre Manual InlineLean
open ConceptualMathematics
open CategoryTheory


#doc (Manual) "Review of 'I-words'" =>

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

This section of the book is primarily a review of material covered in previous Articles and Sessions, but it includes one new definition.

:::definition (definitionTerm := "Involution") (definitionPage := "118")
If $`{f \circ f = 1_A}`, we say $`f` is an _involution_.
:::

We implement `Involution` and `IsInvolution` in Lean as follows:

```savedComment
Involution, IsInvolution
```

```savedLean
structure Involution {𝒞 : Type u} [Category.{v, u} 𝒞] (A : 𝒞) where
  f : A ⟶ A
  invol : f ⊚ f = 𝟙 A

class IsInvolution {𝒞 : Type u} [Category.{v, u} 𝒞] {A : 𝒞}
    (f : A ⟶ A) where
  invol : f ⊚ f = 𝟙 A
```

```savedLean -show
end CM
```
