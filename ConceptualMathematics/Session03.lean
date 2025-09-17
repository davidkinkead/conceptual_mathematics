import VersoManual
import ConceptualMathematics.Meta.Lean
import ConceptualMathematics.Article1
import ConceptualMathematics.Session02
import Mathlib

open Verso.Genre Manual InlineLean
open ConceptualMathematics
open CategoryTheory


#doc (Manual) "Session 3: Composing maps and counting maps" =>

```savedImport
import ConceptualMathematics.Article1
import ConceptualMathematics.Session02
import Mathlib
open CategoryTheory
```

```savedLean (show := false)
namespace CM
local notation:80 g " ⊚ " f:80 => CategoryStruct.comp f g
```

_Category_ having been defined at the end of Article I, we now generally implement _maps_ in the book as Lean _morphisms_.

:::question (questionTitle := "Exercise 1") (questionPage := "36")
$`A`, $`B`, and $`C` are three different sets (or even three different objects in any category); $`f`, $`g`, $`h`, and $`k` are maps with domains and codomains as follows:
$$`A \xrightarrow{f} B, \quad B \xrightarrow{g} A, \quad A \xrightarrow{h} C, \quad C \xrightarrow{k} B.`
Two of the expressions below make sense. Find each of the two, and say what its domain and codomain are:
$$`\text{(a)}\; k \circ h \circ g \circ f, \quad\text{(b)}\; k \circ f \circ g, \quad\text{(c)}\; g \circ f \circ g \circ k \circ h.`
:::

:::solution (solutionTo := "Exercise 1")
```savedComment
Exercise 3.1 (p. 36)
```

```savedLean (show := false)
namespace Ex3_1
```

```savedLean
variable {𝒞 : Type*} [Category 𝒞] {A B C : 𝒞}
         (f : A ⟶ B) (g : B ⟶ A) (h : A ⟶ C) (k : C ⟶ B)
```

(a) makes sense, with domain $`A` and codomain $`B`.

```savedLean (name := out3_1_a)
#check k ⊚ h ⊚ g ⊚ f
```

```leanOutput out3_1_a
k ⊚ h ⊚ g ⊚ f : A ⟶ B
```

(b) does not make sense, since the codomain of $`{f \circ g}` is $`B`, but the domain of $`k` is $`C`.

```savedLean (name := out3_1_b)
#check f ⊚ g
```

```leanOutput out3_1_b
f ⊚ g : B ⟶ B
```

(c) makes sense, with domain $`A` and codomain $`A`.

```savedLean (name := out3_1_c)
#check g ⊚ f ⊚ g ⊚ k ⊚ h
```

```leanOutput out3_1_c
g ⊚ f ⊚ g ⊚ k ⊚ h : A ⟶ A
```

```savedLean (show := false)
end Ex3_1
```
:::

```savedLean (show := false)
end CM
```
