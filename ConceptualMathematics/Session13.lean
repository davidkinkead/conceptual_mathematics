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
import Mathlib

open Verso.Genre Manual InlineLean
open ConceptualMathematics
open CategoryTheory


#doc (Manual) "Session 13: Monoids" =>

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
import Mathlib
open CategoryTheory
```

```savedLean -show
namespace CM
local notation:80 g " ⊚ " f:80 => CategoryStruct.comp f g
```

:::definition (definitionTerm := "Monoid") (definitionPage := "166")
A category with exactly one object is called a _monoid_.
:::

The corresponding mathlib definition is CategoryTheory.SingleObj, which is an abbreviation for Quiver.SingleObj. We print both below for reference.

```lean (name := out_SingleObj)
#print SingleObj
```

```leanOutput out_SingleObj
@[reducible] def CategoryTheory.SingleObj.{u_1} : Type u_1 → Type :=
Quiver.SingleObj
```

```lean (name := out_Quiver_SingleObj)
#print Quiver.SingleObj
```

```leanOutput out_Quiver_SingleObj
def Quiver.SingleObj.{u_1} : Type u_1 → Type :=
fun x ↦ Unit
```

```savedLean -show
end CM
```
