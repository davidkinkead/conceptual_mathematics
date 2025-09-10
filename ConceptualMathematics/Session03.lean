import VersoManual
import ConceptualMathematics.Meta.Lean
import ConceptualMathematics.Article1
import Mathlib

open Verso.Genre Manual InlineLean
open ConceptualMathematics
open CategoryTheory


#doc (Manual) "Session 3: Composing maps and counting maps" =>

```savedImport
import ConceptualMathematics.Article1
import Mathlib
open CategoryTheory
```

```savedLean (show := false)
namespace CM
local notation:80 g " ⊚ " f:80 => CategoryStruct.comp f g
```

_Category_ having been defined at the end of Article I, we now generally implement _maps_ in the book as Lean _morphisms_.

*Exercise 1* (p. 36)

A, B, and C are three different sets (or even three different objects in any category); f, g, h, and k are maps with domains and codomains as follows:

f : A ⟶ B, g : B ⟶ A, h : A ⟶ C, k : C ⟶ B

Two of the expressions below make sense. Find each of the two, and say what its domain and codomain are:

(a) k ⊚ h ⊚ g ⊚ f
(b) k ⊚ f ⊚ g
(c) g ⊚ f ⊚ g ⊚ k ⊚ h

```savedComment
Exercise 3.1 (p. 36)
```

```savedLean
namespace Ex3_1

variable {𝒞 : Type*} [Category 𝒞] {A B C : 𝒞}
         (f : A ⟶ B) (g : B ⟶ A) (h : A ⟶ C) (k : C ⟶ B)
```

```savedLean (name := out3_1_a)
#where -- FIXME initial comment suppressed unless preceeded by command
/- (a) makes sense, with domain A and codomain B. -/

#check k ⊚ h ⊚ g ⊚ f
```

```leanOutput out3_1_a
k ⊚ h ⊚ g ⊚ f : A ⟶ B
```

```savedLean (name := out3_1_b)
#where -- FIXME initial comment suppressed unless preceeded by command
/- (b) does not make sense, since the codomain of f ⊚ g is B, but the
domain of k is C. -/

#check f ⊚ g
```

```leanOutput out3_1_b
f ⊚ g : B ⟶ B
```

```savedLean (name := out3_1_c)
#where -- FIXME initial comment suppressed unless preceeded by command
/- (c) makes sense, with domain A and codomain A. -/

#check g ⊚ f ⊚ g ⊚ k ⊚ h
```

```leanOutput out3_1_c
g ⊚ f ⊚ g ⊚ k ⊚ h : A ⟶ A
```

```savedLean
end Ex3_1
```

```savedLean (show := false)
end CM
```
