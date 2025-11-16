import VersoManual
import ConceptualMathematics.Meta.Lean
import ConceptualMathematics.Html.Css
import ConceptualMathematics.Article1
import ConceptualMathematics.Session02
import ConceptualMathematics.Session03
import ConceptualMathematics.Article2
import ConceptualMathematics.Session04
import ConceptualMathematics.Session05
import ConceptualMathematics.Session09
import ConceptualMathematics.Quiz
import ConceptualMathematics.SummaryQuiz
import ConceptualMathematics.Summary
import ConceptualMathematics.Review
import ConceptualMathematics.Test1
import ConceptualMathematics.Session10
import ConceptualMathematics.Article3
import ConceptualMathematics.Session11
import ConceptualMathematics.Session12
import ConceptualMathematics.Session13
import ConceptualMathematics.Session14
import ConceptualMathematics.Session15
import Mathlib

open Verso.Genre Manual InlineLean
open ConceptualMathematics
open CategoryTheory


#doc (Manual) "A Lean Companion to Conceptual Mathematics" =>

%%%
authors := ["David Kinkead"]
%%%

This _Companion_, which shamelessly steals its title and a fair bit of its approach from Terence Tao's [formalisation](https://github.com/teorth/analysis) of his [_Analysis I_](https://terrytao.wordpress.com/books/analysis-i/) textbook, is intended to be used alongside the second edition of Lawvere and Schanuel's [_Conceptual Mathematics_](https://www.cambridge.org/gb/universitypress/subjects/mathematics/logic-categories-and-sets/conceptual-mathematics-first-introduction-categories-2nd-edition?format=PB&isbn=9780521719162). The _Companion_ aims to formalise most of the definitions, theorems, and exercises in _Conceptual Mathematics_ using Lean 4 and mathlib, but reproduces almost none of the text from the book itself and consequently has little value on its own.

When formalising the definitions in the book, I have tried to use the corresponding definitions in mathlib where I was able to find them, rather than reinventing too many wheels. For the exercises, I have generally stayed faithful to the wording in the book, but I have taken some small liberties where I felt doing so would allow a solution to reflect more clearly the core concerns of the question (for instance, by a frequent use of types instead of sets). I have flagged any such deviations in the comments.

I have attempted to strike a balance throughout between ease of reading and optimised, idiomatic Lean code, but wherever needed have erred (I hope!) on the side of readability. In particular, I have largely avoided the use of the `simp` tactic and other automation, in order to make the logical steps in the proofs as explicit as possible.

This _Companion_ is the result of a project I undertook to learn both Lean and some elementary category theory at the same time (and ultimately a decent amount about Verso too). It remains a work in progress. It will contain plenty of opportunities for improvement and more than a few errors! I welcome any comments, suggestions, corrections, or contributions. Please feel free to open an issue or a pull request on the [GitHub repository](https://github.com/davidkinkead/conceptual_mathematics).

To learn more about Lean and mathlib, please visit the wonderful [Lean community website](https://leanprover-community.github.io/).

Of particular relevance to this _Companion_ is the high-level overview of [category theory in mathlib](https://leanprover-community.github.io/theories/category_theory.html) hosted on the community site, which provides a helpful jumping-off point and also covers some of the key notation.

Regarding notation, it is worth mentioning that composition of morphisms in mathlib uses the notation `≫` (`\gg`), as in `f ≫ g`, which means "$`f` _followed by_ $`g`". To align with the book and to follow the usual convention, however, we introduce the notation `⊚` (`\oo`), as in `f ⊚ g`, which means "$`f` _following_ $`g`":

```lean
local notation:80 g " ⊚ " f:80 => CategoryStruct.comp f g
```

(This approach is suggested on the high-level overview page mentioned in the previous paragraph as well as elsewhere in the mathlib documentation.)

All page references given in this _Companion_ are to Lawvere, F.W. and Schanuel, S.H. (2009) _Conceptual mathematics: a first introduction to categories_. 2nd edn. Cambridge: Cambridge University Press.

{include 2 ConceptualMathematics.Article1}

{include 2 ConceptualMathematics.Session02}

{include 2 ConceptualMathematics.Session03}

{include 2 ConceptualMathematics.Article2}

{include 2 ConceptualMathematics.Session04}

{include 2 ConceptualMathematics.Session05}

{include 2 ConceptualMathematics.Session09}

{include 2 ConceptualMathematics.Quiz}

{include 2 ConceptualMathematics.SummaryQuiz}

{include 2 ConceptualMathematics.Summary}

{include 2 ConceptualMathematics.Review}

{include 2 ConceptualMathematics.Test1}

{include 2 ConceptualMathematics.Session10}

{include 2 ConceptualMathematics.Article3}

{include 2 ConceptualMathematics.Session11}

{include 2 ConceptualMathematics.Session12}

{include 2 ConceptualMathematics.Session13}

{include 2 ConceptualMathematics.Session14}

{include 2 ConceptualMathematics.Session15}
