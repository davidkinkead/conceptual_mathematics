import VersoManual
import ConceptualMathematics.Meta.Lean
import ConceptualMathematics.Article1
import ConceptualMathematics.Session03
import ConceptualMathematics.Article2
import ConceptualMathematics.Session04
import ConceptualMathematics.Session05
import ConceptualMathematics.Session09
import ConceptualMathematics.Summary
import Mathlib

open Verso.Genre Manual InlineLean
open ConceptualMathematics
open CategoryTheory


#doc (Manual) "Review of 'I-words'" =>

```savedImport
import ConceptualMathematics.Article1
import ConceptualMathematics.Session03
import ConceptualMathematics.Article2
import ConceptualMathematics.Session04
import ConceptualMathematics.Session05
import ConceptualMathematics.Session09
import ConceptualMathematics.Summary
import Mathlib
open CategoryTheory
```

```savedLean (show := false)
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
structure Involution {𝒞 : Type*} [Category 𝒞] (A : 𝒞) where
  f : A ⟶ A
  invol : f ⊚ f = 𝟙 A

class IsInvolution {𝒞 : Type*} [Category 𝒞] {A : 𝒞} (f : A ⟶ A) where
  invol : f ⊚ f = 𝟙 A
```

```savedLean (show := false)
end CM
```
