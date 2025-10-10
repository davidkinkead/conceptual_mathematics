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


#doc (Manual) "Session 10: Brouwer's theorems" =>

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

```savedLean (show := false)
namespace CM
local notation:80 g " ⊚ " f:80 => CategoryStruct.comp f g
```

:::theoremDirective (theoremTitle := "Brouwer fixed point theorem (1)") (theoremPage := "120")
Let $`I` be a line segment, including its endpoints ($`I` for Interval) and suppose that $`{f : I \rightarrow I}` is a continuous endomap. Then this map must have a fixed point: a point $`x` in $`I` for which $`{f(x) = x}`.
:::

TODO Brouwer fixed point theorem (1)

:::theoremDirective (theoremTitle := "Brouwer fixed point theorem (2)") (theoremPage := "121")
Let $`D` be a closed disk (the plane figure consisting of all the points inside or on a circle), and $`f` a continuous endomap of $`D`. Then $`f` has a fixed point.
:::

TODO Brouwer fixed point theorem (2)

:::theoremDirective (theoremTitle := "Brouwer fixed point theorem (3)") (theoremPage := "122")
Any continuous endomap of a solid ball has a fixed point.
:::

TODO Brouwer fixed point theorem (3)

:::theoremDirective (theoremTitle := "Brouwer retraction theorem (I)") (theoremPage := "122")
Consider the inclusion map $`{j : E \rightarrow I}` of the two-point set $`E` as boundary of the interval $`I`. There is no continuous map which is a retraction for $`j`.
:::

TODO Brouwer retraction theorem (I)

:::theoremDirective (theoremTitle := "Brouwer retraction theorem (II)") (theoremPage := "123")
Consider the inclusion map $`{j : C \rightarrow D}` of the circle $`C` as boundary of the disk $`D` into the disk. There is no continuous map which is a retraction for $`j`.
:::

TODO Brouwer retraction theorem (II)

:::theoremDirective (theoremTitle := "Brouwer retraction theorem (III)") (theoremPage := "123")
Consider the inclusion $`{j : S \rightarrow B}` of the sphere $`S` as boundary of the ball $`B` into the ball. There is no continuous map which is a retraction for $`j`.
:::

TODO Brouwer retraction theorem (III)

:::question (questionTitle := "Exercise 1") (questionPage := "126")
Let $`{j : C \rightarrow D}` be, as before, the inclusion of the circle into the disk. Suppose that we have two continuous maps $`{D \xrightarrow{f} D}` \[and\] $`{D \xrightarrow{g} D}`, and that $`g` satisfies $`{g \circ j = j}`. Use the retraction theorem to show that there must be a point $`x` in the disk at which $`{f(x) = g(x)}`. (Hint: The fixed point theorem is the special case $`{g = 1_D}`, so try to generalize the argument we used in that special case.)
:::

:::solution (solutionTo := "Exercise 1")
```savedComment
Exercise 10.1 (p. 126)
```

TODO Exercise 10.1
:::

:::question (questionTitle := "Exercise 2") (questionPage := "126")
Suppose that $`A` is a 'retract' of $`X`, i.e. there are maps $`{A \xrightarrow{s} X \xrightarrow{r} A}` with $`{r \circ s = 1_A}`. Suppose also that $`X` has the fixed point property for maps from T, i.e. for every endomap $`{X \xrightarrow{f} X}`, there is a map $`{T \xrightarrow{x} X}` for which $`{f x = x}`. Show that $`A` also has the fixed point property for maps from T. (Hint: The proof should work in any category, so it should only use the algebra of composition of maps.)
:::

:::solution (solutionTo := "Exercise 2")
```savedComment
Exercise 10.2 (p. 126)
```

TODO Exercise 10.2
:::

:::question (questionTitle := "Exercise 3") (questionPage := "126")
Use the result of the preceding exercise, and the fact that the antipodal map has no fixed point, to deduce each retraction theorem from the corresponding fixed point theorem.
:::

:::solution (solutionTo := "Exercise 3")
```savedComment
Exercise 10.3 (p. 126)
```

TODO Exercise 10.3
:::

:::theoremDirective (theoremTitle := "Axiom 1") (theoremPage := "128")
If $`T` is any object in 𝑪, and $`{T \xrightarrow{a} A}` and $`{T \xrightarrow{s} S}` are maps satisfying $`{h a = j s}`, then $`{p a = s}`.
:::

```savedComment
Axiom 1 (p. 128)
```

TODO Axiom 1

:::theoremDirective (theoremTitle := "Theorem 1") (theoremPage := "128")
If $`{B \xrightarrow{\alpha} A}` satisfies $`{h \alpha j = j}`, then $`{p \alpha}` is a retraction for $`j`.
:::

:::proof (proofPage := "128")
Put $`{T = S}`, $`{s = 1_S}`, and $`{a = \alpha j}` in Axiom 1.
:::

```savedComment
Theorem 1 (p. 128)
```

TODO Theorem 1

:::theoremDirective (theoremTitle := "Corollary 1") (theoremPage := "128")
If $`{h \alpha = 1_B}`, then $`{p \alpha}` is a retraction for $`j`.
:::

```savedComment
Corollary 1 (p. 128)
```

TODO Corollary 1

:::theoremDirective (theoremTitle := "Axiom 2") (theoremPage := "129")
If $`T` is any object in 𝑪, and $`{T \xrightarrow{f} B}` \[and\] $`{T \xrightarrow{g} B}` are any maps, then either there is a point $`{\mathbf{1} \xrightarrow{t} T}` with $`{f t = g t}`, or there is a map $`{T \xrightarrow{\alpha} A}` with $`{h \alpha = g}`.
:::

```savedComment
Axiom 2 (p. 129)
```

TODO Axiom 2

:::theoremDirective (theoremTitle := "Theorem 2") (theoremPage := "129")
Suppose we have maps
$$`B \xrightarrow{f} B\\\
B \xrightarrow{g} B`
and $`{g j = j}`, then either there is a point $`{\mathbf{1} \xrightarrow{b} B}` with $`{f b = g b}`, or there is a retraction for $`{S \xrightarrow{j} B}`.
:::

:::proof (proofPage := "129")
Take $`{T = B}` in Axiom 2. We get: either there is a point $`{\mathbf{1} \xrightarrow{b} B}` with $`{f b = g b}`, or there is a map $`{B \xrightarrow{\alpha} A}` with $`{h \alpha = g}`; but then $`{h \alpha j = g j = j}`, so Theorem 1 says that $`{p \alpha}` is a retraction for $`j`.
:::

```savedComment
Theorem 2 (p. 129)
```

TODO Theorem 2

:::theoremDirective (theoremTitle := "Corollary 2") (theoremPage := "129")
If $`{B \xrightarrow{f} B}`, then either there is a fixed point for $`f` or there is a retraction for $`{S \xrightarrow{j} B}`.
:::

```savedComment
Corollary 2 (p. 129)
```

TODO Corollary 2

:::question (questionTitle := "Exercise 4") (questionPage := "132")
(a) Express the restrictions given above on my travel and yours by equations involving composition of maps, introducing other objects and maps as needed.

(b) Formulate the conclusion that at some time we meet, in terms of composition of maps. (You will need to introduce the object $`\mathbf{1}`.)

(c) Guess a stronger version of Brouwer’s fixed point theorem in two dimensions, by replacing $`E`, $`I`, and $`R` by the circle, disk, and plane. (You can do it in three dimensions too, if you want.)

(d) Try to test your guess in (c); e.g. try to invent maps for which your conjectured theorem is not true.
:::

:::solution (solutionTo := "Exercise 4")
```savedComment
Exercise 10.4 (p. 132)
```

TODO Exercise 10.4
:::

```savedLean (show := false)
end CM
```
