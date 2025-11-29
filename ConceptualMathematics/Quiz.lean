import VersoManual
import ConceptualMathematics.Meta.Lean
import ConceptualMathematics.Article2
import Mathlib

open Verso.Genre Manual InlineLean
open ConceptualMathematics
open CategoryTheory


#doc (Manual) "Quiz" =>

%%%
htmlSplit := .never
number := false
%%%

```savedImport
import ConceptualMathematics.Article2
import Mathlib
open CategoryTheory
```

```savedLean -show
namespace CM
local notation:80 g " ⊚ " f:80 => CategoryStruct.comp f g
```

:::question (questionTitle := "Problem 1") (questionPage := "108")
Give an example of two explicit sets $`A` and $`B` and an explicit map $`{A \xrightarrow{f} B}` satisfying _both_:

(a) there is a retraction for $`f`, _and_

(b) there is _no_ section for $`f`.

Then explain how you know that $`f` satisfies (a) and (b).
:::

:::solution (solutionTo := "Problem 1")
```savedComment
Problem Quiz.1 (p. 108)
```

We use `Fintype`s here instead of sets.

```savedLean -show
namespace Quiz_1
```

We give explicit types $`A` and $`B` and an explicit map $`f`.

```savedLean
inductive A
  | a
  deriving Fintype

inductive B
  | b₁ | b₂
  deriving Fintype

def f : A ⟶ B
  | A.a => B.b₁
```

Our candidate retraction for $`f` is

```savedLean
def r : B ⟶ A
  | B.b₁ => A.a
  | B.b₂ => A.a
```

and we show that (a) is satisfied.

```savedLean
example : IsRetraction f := by
  use r
  change r ⊚ f = 𝟙 A
  funext x
  fin_cases x
  dsimp [f, r]
```

We show that $`f` also satisfies (b).

```savedLean
example : ¬(IsSection f) := by
  by_contra h
  obtain ⟨s, hs⟩ := h
  have h_false := congrFun hs B.b₂
  cases h_false
```

```savedLean -show
end Quiz_1
```
:::

:::question (questionTitle := "Problem 2") (questionPage := "108")
If $`{C \xrightarrow{p} D \xrightarrow{q} C}` satisfy $`{p \circ q \circ p = p}`, can you conclude that

(a) $`{p \circ q}` is idempotent? If so, how?

(b) $`{q \circ p}` is idempotent? If so, how?
:::

:::solution (solutionTo := "Problem 2")
```savedComment
Problem Quiz.2 (p. 108)
```

```savedLean -show
namespace Quiz_2
```

```savedLean
variable {𝒞 : Type u} [Category.{v, u} 𝒞] {C D : 𝒞}
         (p : C ⟶ D) (q : D ⟶ C) (hpq : p ⊚ q ⊚ p = p)
```

We show that $`{p \circ q}` is idempotent.

```savedLean
example : IsIdempotent (p ⊚ q) := {
  idem := by
    calc (p ⊚ q) ⊚ p ⊚ q
      _ = ((p ⊚ q) ⊚ p) ⊚ q := by rw [Category.assoc]
      _ = (p ⊚ q ⊚ p) ⊚ q := by rw [← Category.assoc p]
      _ = p ⊚ q := by rw [hpq]
}
```

We show that $`{q \circ p}` is idempotent.

```savedLean
example : IsIdempotent (q ⊚ p) := {
  idem := by
    calc (q ⊚ p) ⊚ q ⊚ p
      _ = q ⊚ p ⊚ q ⊚ p := by rw [Category.assoc (q ⊚ p)]
      _ = q ⊚ p := by rw [hpq]
}
```

```savedLean -show
end Quiz_2
```
:::

# Optional questions

:::question (questionTitle := "Problem 2*") (questionPage := "108")
If $`{C \xrightarrow{p} D \xrightarrow{q} C}` satisfy $`{p \circ q \circ p = p}`, use the given maps $`p` and $`q` to devise a map $`q'` satisfying _both_:
$$`p \circ q' \circ p = p`
_and_
$$`q' \circ p \circ q' = q'`
(and explain how you know that your $`q'` has these properties).
:::

:::solution (solutionTo := "Problem 2*")
```savedComment
Problem Quiz_2* (p. 108)
```

```savedLean -show
namespace «Quiz_2*»
```

```savedLean
variable {𝒞 : Type u} [Category.{v, u} 𝒞] {C D : 𝒞}
         (p : C ⟶ D) (q : D ⟶ C) (hpq : p ⊚ q ⊚ p = p)
```

We show that $`{q' = q \circ p \circ q}` has the required properties.

```savedLean
example : ∃ q', p ⊚ q' ⊚ p = p ∧ q' ⊚ p ⊚ q' = q' := by
  use q ⊚ p ⊚ q -- q'
  constructor
  · rw [← Category.assoc p, ← Category.assoc, hpq, hpq]
  · rw [Category.assoc (q ⊚ p ⊚ q)]
    repeat rw [← Category.assoc p]
    rw [hpq]
    repeat rw [Category.assoc q]
    rw [← Category.assoc (q ⊚ p), hpq]
```

```savedLean -show
end «Quiz_2*»
```
:::

:::question (questionTitle := "Problem 1*") (questionPage := "108")
Same question as Problem 1 at top of page, except that both sets $`A` and $`B` are required to be _infinite_ sets.
:::

:::solution (solutionTo := "Problem 1*")
```savedComment
Problem Quiz_1* (p. 108)
```

We use (non-finite) types here instead of infinite sets.

```savedLean -show
namespace «Quiz_1*»
```

We give explicit types $`A` and $`B` and an explicit map $`f`.

```savedLean
abbrev A := ℕ
abbrev B := ℝ

def f : A ⟶ B
  | 0 => 0
  | n + 1 => n + 1
```

Our candidate retraction for $`f` is

```savedLean
noncomputable def r : B ⟶ A
  | r => ⌊abs r⌋₊
```

and we show that (a) is satisfied.

```savedLean
example : IsRetraction f := by
  use r
  change r ⊚ f = 𝟙 A
  funext x
  dsimp [f, r]
  induction x with
  | zero => rw [abs_zero, Nat.floor_zero]
  | succ n =>
      dsimp
      norm_cast
      rw [Nat.floor_natCast]
```

We show that $`f` also satisfies (b).

```savedLean
example : ¬(IsSection f) := by
  by_contra h
  obtain ⟨s, hs⟩ := h
  have h_false := congrFun hs 0.5
  cases hx : s 0.5 with
  | zero =>
      rw [types_comp_apply, hx] at h_false
      dsimp [f] at h_false
      linarith
  | succ n =>
      rw [types_comp_apply, hx] at h_false
      dsimp [f] at h_false
      have h_ge_1 : (1 : B) ≤ n + 1 := by linarith
      linarith
```

```savedLean -show
end «Quiz_1*»
```
:::

```savedLean -show
end CM
```
