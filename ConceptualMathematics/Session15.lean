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
import ConceptualMathematics.Session13
import ConceptualMathematics.Session14
import Mathlib

open Verso.Genre Manual InlineLean
open ConceptualMathematics
open CategoryTheory


#doc (Manual) "Session 15: Objectification of properties in dynamical systems" =>

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
import ConceptualMathematics.Session13
import ConceptualMathematics.Session14
import Mathlib
open CategoryTheory
```

```savedLean -show
namespace CM
local notation:80 g " ⊚ " f:80 => CategoryStruct.comp f g
```

# 1. Structure-preserving maps from a cycle to another endomap

:::excerpt (excerptPage := "176")
We say that an element $`y` in $`Y^{↻\beta}` has _period_ four if $`{\beta^4(y) = y}`. All elements that have period one or two are _included_ in this, because if $`{\beta(y) = y}` or $`{\beta^2(y) = y}`, then also $`{\beta^4(y) = y}`.
:::

```savedComment
Period of an element (p. 176)
```

```savedLean
theorem period_four_of_period_one {Y : Type} (β : End Y) (y : Y)
    : β y = y → (β ^ 4) y = y := by
  intro hβ
  nth_rw 2 [← hβ, ← hβ, ← hβ, ← hβ]
  rfl

theorem period_four_of_period_two {Y : Type} (β : End Y) (y : Y)
    : (β ^ 2) y = y → (β ^ 4) y = y := by
  intro hβ2
  nth_rw 2 [← hβ2, ← hβ2]
  rfl
```

# 2. Naming the elements that have a given period by maps

:::question (questionTitle := "Exercise 1") (questionPage := "177")
Show that an element which has both period 5 and period 7 must be a fixed point.
:::

:::solution (solutionTo := "Exercise 1")
```savedComment
Exercise 15.1 (p. 177)
```

"If an element has any positive period, it must have a smallest period. In fact, all its periods are multiples of this smallest one" (p. 177). Since 5 and 7 are coprime, their only positive common divisor is 1, and so the only element having both period 5 and period 7 is an element having period 1—that is, a fixed point. We proceed via Bézout's identity, $`{7 \times 3 − 5 \times 4 = 1}`.

```savedLean
open Function
example {X : Type} (α : End X) (x : X)
    : (α ^ 5) x = x ∧ (α ^ 7) x = x → α x = x := by
  rintro ⟨h5, h7⟩
  change α^[5] x = x at h5
  change α^[7] x = x at h7
  nth_rw 1 [← h5, ← h5, ← h5, ← h5, ← iterate_one α]
  nth_rw 2 [← h7, ← h7, ← h7]
  repeat rw [← iterate_add_apply α 5 _ x]
  rw [← iterate_add_apply α 1 20 x]
  repeat rw [← iterate_add_apply α 7 _ x]
```
:::

# 3. Naming arbitrary elements

We implement the 'successor map' $`\sigma : \mathbb{N} \rightarrow \mathbb{N}` defined by $`\sigma(n) = n+1` (p. 178) as follows:

```savedComment
Successor map (p. 178)
```

```savedLean
def σ : ℕ ⟶ ℕ := (· + 1)

def ℕσ : SetWithEndomap := {
  t := ℕ
  carrier := Set.univ
  toEnd := σ
  toEnd_mem := fun _ ↦ Set.mem_univ _
}
```

:::question (questionTitle := "Exercise 2") (questionPage := "178")
Find all the maps from $`\mathbb{N}^{↻\sigma}` to $`C_4`, the cycle of length 4.
:::

:::solution (solutionTo := "Exercise 2")
```savedComment
Exercise 15.2 (p. 178)
```

```savedLean -show
namespace Ex15_2
```

We define $`C_4` as follows:

```savedLean
def ς : Fin 4 ⟶ Fin 4 := (· + 1)

def C₄ : SetWithEndomap := {
  t := Fin 4
  carrier := Set.univ
  toEnd := ς
  toEnd_mem := fun _ ↦ Set.mem_univ _
}
```

Then there are four distinct maps from $`\mathbb{N}^{↻\sigma}` to $`C_4`. We give these maps below, in each case showing that we can form a valid morphism in the category 𝑺↻.

```savedLean
def f₀ : ℕσ.t ⟶ C₄.t
  | Nat.zero => (0 : Fin 4) -- f(0) = 0
  | n + 1 => ς (f₀ n)

def f₀' : ℕσ ⟶ C₄ := ⟨
  f₀,
  by
    constructor
    · exact fun _ _ ↦ Set.mem_univ _
    · funext x
      dsimp [f₀, ℕσ, C₄, σ, ς]
⟩

def f₁ : ℕσ.t ⟶ C₄.t
  | Nat.zero => (1 : Fin 4) -- f(0) = 1
  | n + 1 => ς (f₁ n)

def f₁' : ℕσ ⟶ C₄ := ⟨
  f₁,
  by
    constructor
    · exact fun _ _ ↦ Set.mem_univ _
    · funext x
      dsimp [f₁, ℕσ, C₄, σ, ς]
⟩

def f₂ : ℕσ.t ⟶ C₄.t
  | Nat.zero => (2 : Fin 4) -- f(0) = 2
  | n + 1 => ς (f₂ n)

def f₂' : ℕσ ⟶ C₄ := ⟨
  f₂,
  by
    constructor
    · exact fun _ _ ↦ Set.mem_univ _
    · funext x
      dsimp [f₂, ℕσ, C₄, σ, ς]
⟩

def f₃ : ℕσ.t ⟶ C₄.t
  | Nat.zero => (3 : Fin 4) -- f(0) = 3
  | n + 1 => ς (f₃ n)

def f₃' : ℕσ ⟶ C₄ := ⟨
  f₃,
  by
    constructor
    · exact fun _ _ ↦ Set.mem_univ _
    · funext x
      dsimp [f₃, ℕσ, C₄, σ, ς]
⟩
```

```savedLean -show
end Ex15_2
```
:::

:::question (questionTitle := "Exercise 3") (questionPage := "179")
Show that _evaluation at 0_ and _iteration_ are inverse (to each other).
:::

:::solution (solutionTo := "Exercise 3")
```savedComment
Exercise 15.3 (p. 179)
```

{htmlSpan (class := "todo")}[TODO Exercise 15.3]
:::

:::question (questionTitle := "Exercise 4") (questionPage := "179")
For any dynamical system $`X^{↻\alpha}`, show that $`\alpha` is itself a map of dynamical systems $`{X^{↻\alpha} \xrightarrow{\alpha} X^{↻\alpha}}`.
:::

:::solution (solutionTo := "Exercise 4")
```savedComment
Exercise 15.4 (p. 179)
```

```savedLean -show
namespace Ex15_4
```

Essentially, the exercise is asking for a proof that `α ⊚ α = α ⊚ α`, which is trivially true.

```savedLean
variable (X : Type) (α : X ⟶ X)

def Xα : SetWithEndomap := {
  t := X
  carrier := Set.univ
  toEnd := α
  toEnd_mem := fun _ ↦ Set.mem_univ _
}

example : α ⊚ (Xα X α).toEnd = (Xα X α).toEnd ⊚ α := rfl
```

```savedLean -show
end Ex15_4
```
:::

:::question (questionTitle := "Exercise 5") (questionPage := "179")
Show that if $`{\mathbb{N}^{↻\sigma} \xrightarrow{f} Y^{↻\beta}}` corresponds to $`y`, then $`{\mathbb{N}^{↻\sigma} \xrightarrow{f \circ \sigma} Y^{↻\beta}}` corresponds to $`\beta(y)`.
:::

:::solution (solutionTo := "Exercise 5")
```savedComment
Exercise 15.5 (p. 179)
```

```savedLean
example (Yβ : SetWithEndomap) (f : ℕσ ⟶ Yβ) (y : Yβ.t)
    (hy : f.val (0 : ℕ) = y)
    : (f.val ⊚ σ) (0 : ℕ) = Yβ.toEnd y := by
  obtain ⟨f, _, hf_comm⟩ := f
  have h0 : ℕσ.toEnd (0 : ℕ) = (1 : ℕ) := rfl
  rw [← hy]
  dsimp [σ]
  rw [← types_comp_apply _ Yβ.toEnd, ← hf_comm, types_comp_apply, h0]
```
:::

# 4. The philosophical role of _N_

:::question (questionTitle := "Exercise 6") (questionPage := "181")
Show that the gender map $`{X^{↻m} \xrightarrow{g} B}` is a map in the category 𝑺↻.
:::

:::solution (solutionTo := "Exercise 6")
```savedComment
Exercise 15.6 (p. 181)
```

```savedLean -show
namespace Ex15_6
```

cf. Session 12, Exercise 3.

```savedLean
inductive B
  | female | male

def β : B ⟶ B
  | B.female => B.female
  | B.male => B.female

inductive ParentType
  | isMother

structure Person where
  parentType : ParentType

def m : Person ⟶ Person := fun _ ↦ ⟨ParentType.isMother⟩

def Xm : SetWithEndomap := {
  t := Person
  carrier := Set.univ
  toEnd := m
  toEnd_mem := fun _ ↦ Set.mem_univ _
}
```

We define the gender map $`g` and show that it commutes (i.e., is a map in the category 𝑺↻).

```savedLean
def g : Xm.t ⟶ B
  | ⟨ParentType.isMother⟩ => B.female

example : g ⊚ Xm.toEnd = β ⊚ g := rfl
```

Equivalently, taking $`B` as an object in the category 𝑺↻, we can show that $`g` forms a valid morphism.

```savedLean
def Bβ : SetWithEndomap := {
  t := B
  carrier := Set.univ
  toEnd := β
  toEnd_mem := fun _ ↦ Set.mem_univ _
}

def g' : Xm ⟶ Bβ := ⟨
  g,
  by
    constructor
    · exact fun _ _ ↦ Set.mem_univ _
    · rfl
⟩
```

```savedLean -show
end Ex15_6
```
:::

# 5. Presentations of dynamical systems

:::question (questionTitle := "Exercise 7") (questionPage := "185")
```savedComment
Exercise 15.7 (p. 185)
```

```savedLean -show
namespace Ex15_7
```

Find all the maps from the $`X^{↻\alpha}` \[below\] to the $`Y^{↻\beta}` \[below\]. (Unless I made a mistake, there are 14 of them.)

```savedLean
inductive X
  | a | a₁ | a₂ | a₃ | a₄ | b | c | d | d₁

-- Subscripts correspond to powers of α
-- (i.e., the number of applications of α to the element)
def α : X ⟶ X
  | X.a => X.a₁
  | X.a₁ => X.a₂
  | X.a₂ => X.a₃
  | X.a₃ => X.a₄
  | X.a₄ => X.a₂
  | X.b => X.a₂
  | X.c => X.a₃
  | X.d => X.d₁
  | X.d₁ => X.d

inductive Y
  | l | m | p | q | r | s | t | u | v | w | x | y | z

def β : Y ⟶ Y
  | Y.l => Y.m
  | Y.m => Y.l
  | Y.p => Y.r
  | Y.q => Y.r
  | Y.r => Y.t
  | Y.s => Y.t
  | Y.t => Y.v
  | Y.u => Y.s
  | Y.v => Y.u
  | Y.w => Y.x
  | Y.x => Y.y
  | Y.y => Y.w
  | Y.z => Y.y

def Xα : SetWithEndomap := {
  t := X
  carrier := Set.univ
  toEnd := α
  toEnd_mem := fun _ ↦ Set.mem_univ _
}

def Yβ : SetWithEndomap := {
  t := Y
  carrier := Set.univ
  toEnd := β
  toEnd_mem := fun _ ↦ Set.mem_univ _
}
```
:::

::::solution (solutionTo := "Exercise 7")
It is possible the book does in fact contain a mistake here. Following the algorithm given on pp. 182–185, I find only 12 distinct maps, not 14. The 12 maps are given below, in each case with a proof that the map forms a valid morphism $`{X^{↻\alpha} \rightarrow Y^{↻\beta}}`.

:::htmlDiv («class» := "compact")
Map 1:

(i) $`\bar{a} = w` satisfies $`\beta^5\bar{a} = \beta^2\bar{a}`

(ii) $`\bar{b} = x` satisfies $`\beta\bar{b} = \beta^2\bar{a}`

(iii) $`\bar{c} = y` satisfies $`\beta\bar{c} = \beta^3\bar{a}`

(iv) $`\bar{d} = l` satisfies $`\beta^2\bar{d} = \bar{d}`
:::

```savedLean
def f₁ : Xα.t ⟶ Yβ.t
  | X.a => Y.w
  | X.a₁ => Y.x
  | X.a₂ => Y.y
  | X.a₃ => Y.w
  | X.a₄ => Y.x
  | X.b => Y.x
  | X.c => Y.y
  | X.d => Y.l
  | X.d₁ => Y.m

def f₁' : Xα ⟶ Yβ := ⟨
  f₁,
  by
    constructor
    · exact fun _ _ ↦ Set.mem_univ _
    · funext x
      cases x <;> rfl
⟩
```

:::htmlDiv («class» := "compact")
Map 2:

(i) $`\bar{a} = w` satisfies $`\beta^5\bar{a} = \beta^2\bar{a}`

(ii) $`\bar{b} = x` satisfies $`\beta\bar{b} = \beta^2\bar{a}`

(iii) $`\bar{c} = y` satisfies $`\beta\bar{c} = \beta^3\bar{a}`

(iv) $`\bar{d} = m` satisfies $`\beta^2\bar{d} = \bar{d}`
:::

```savedLean
def f₂ : Xα.t ⟶ Yβ.t
  | X.a => Y.w
  | X.a₁ => Y.x
  | X.a₂ => Y.y
  | X.a₃ => Y.w
  | X.a₄ => Y.x
  | X.b => Y.x
  | X.c => Y.y
  | X.d => Y.m
  | X.d₁ => Y.l

def f₂' : Xα ⟶ Yβ := ⟨
  f₂,
  by
    constructor
    · exact fun _ _ ↦ Set.mem_univ _
    · funext x
      cases x <;> rfl
⟩
```

:::htmlDiv («class» := "compact")
Map 3:

(i) $`\bar{a} = w` satisfies $`\beta^5\bar{a} = \beta^2\bar{a}`

(ii) $`\bar{b} = z` satisfies $`\beta\bar{b} = \beta^2\bar{a}`

(iii) $`\bar{c} = y` satisfies $`\beta\bar{c} = \beta^3\bar{a}`

(iv) $`\bar{d} = l` satisfies $`\beta^2\bar{d} = \bar{d}`
:::

```savedLean
def f₃ : Xα.t ⟶ Yβ.t
  | X.a => Y.w
  | X.a₁ => Y.x
  | X.a₂ => Y.y
  | X.a₃ => Y.w
  | X.a₄ => Y.x
  | X.b => Y.z
  | X.c => Y.y
  | X.d => Y.l
  | X.d₁ => Y.m

def f₃' : Xα ⟶ Yβ := ⟨
  f₃,
  by
    constructor
    · exact fun _ _ ↦ Set.mem_univ _
    · funext x
      cases x <;> rfl
⟩
```

:::htmlDiv («class» := "compact")
Map 4:

(i) $`\bar{a} = w` satisfies $`\beta^5\bar{a} = \beta^2\bar{a}`

(ii) $`\bar{b} = z` satisfies $`\beta\bar{b} = \beta^2\bar{a}`

(iii) $`\bar{c} = y` satisfies $`\beta\bar{c} = \beta^3\bar{a}`

(iv) $`\bar{d} = m` satisfies $`\beta^2\bar{d} = \bar{d}`
:::

```savedLean
def f₄ : Xα.t ⟶ Yβ.t
  | X.a => Y.w
  | X.a₁ => Y.x
  | X.a₂ => Y.y
  | X.a₃ => Y.w
  | X.a₄ => Y.x
  | X.b => Y.z
  | X.c => Y.y
  | X.d => Y.m
  | X.d₁ => Y.l

def f₄' : Xα ⟶ Yβ := ⟨
  f₄,
  by
    constructor
    · exact fun _ _ ↦ Set.mem_univ _
    · funext x
      cases x <;> rfl
⟩
```

:::htmlDiv («class» := "compact")
Map 5:

(i) $`\bar{a} = x` satisfies $`\beta^5\bar{a} = \beta^2\bar{a}`

(ii) $`\bar{b} = y` satisfies $`\beta\bar{b} = \beta^2\bar{a}`

(iii) $`\bar{c} = w` satisfies $`\beta\bar{c} = \beta^3\bar{a}`

(iv) $`\bar{d} = l` satisfies $`\beta^2\bar{d} = \bar{d}`
:::

```savedLean
def f₅ : Xα.t ⟶ Yβ.t
  | X.a => Y.x
  | X.a₁ => Y.y
  | X.a₂ => Y.w
  | X.a₃ => Y.x
  | X.a₄ => Y.y
  | X.b => Y.y
  | X.c => Y.w
  | X.d => Y.l
  | X.d₁ => Y.m

def f₅' : Xα ⟶ Yβ := ⟨
  f₅,
  by
    constructor
    · exact fun _ _ ↦ Set.mem_univ _
    · funext x
      cases x <;> rfl
⟩
```

:::htmlDiv («class» := "compact")
Map 6:

(i) $`\bar{a} = x` satisfies $`\beta^5\bar{a} = \beta^2\bar{a}`

(ii) $`\bar{b} = y` satisfies $`\beta\bar{b} = \beta^2\bar{a}`

(iii) $`\bar{c} = w` satisfies $`\beta\bar{c} = \beta^3\bar{a}`

(iv) $`\bar{d} = m` satisfies $`\beta^2\bar{d} = \bar{d}`
:::

```savedLean
def f₆ : Xα.t ⟶ Yβ.t
  | X.a => Y.x
  | X.a₁ => Y.y
  | X.a₂ => Y.w
  | X.a₃ => Y.x
  | X.a₄ => Y.y
  | X.b => Y.y
  | X.c => Y.w
  | X.d => Y.m
  | X.d₁ => Y.l

def f₆' : Xα ⟶ Yβ := ⟨
  f₆,
  by
    constructor
    · exact fun _ _ ↦ Set.mem_univ _
    · funext x
      cases x <;> rfl
⟩
```

:::htmlDiv («class» := "compact")
Map 7:

(i) $`\bar{a} = y` satisfies $`\beta^5\bar{a} = \beta^2\bar{a}`

(ii) $`\bar{b} = w` satisfies $`\beta\bar{b} = \beta^2\bar{a}`

(iii) $`\bar{c} = x` satisfies $`\beta\bar{c} = \beta^3\bar{a}`

(iv) $`\bar{d} = l` satisfies $`\beta^2\bar{d} = \bar{d}`
:::

```savedLean
def f₇ : Xα.t ⟶ Yβ.t
  | X.a => Y.y
  | X.a₁ => Y.w
  | X.a₂ => Y.x
  | X.a₃ => Y.y
  | X.a₄ => Y.w
  | X.b => Y.w
  | X.c => Y.x
  | X.d => Y.l
  | X.d₁ => Y.m

def f₇' : Xα ⟶ Yβ := ⟨
  f₇,
  by
    constructor
    · exact fun _ _ ↦ Set.mem_univ _
    · funext x
      cases x <;> rfl
⟩
```

:::htmlDiv («class» := "compact")
Map 8:

(i) $`\bar{a} = y` satisfies $`\beta^5\bar{a} = \beta^2\bar{a}`

(ii) $`\bar{b} = w` satisfies $`\beta\bar{b} = \beta^2\bar{a}`

(iii) $`\bar{c} = x` satisfies $`\beta\bar{c} = \beta^3\bar{a}`

(iv) $`\bar{d} = m` satisfies $`\beta^2\bar{d} = \bar{d}`
:::

```savedLean
def f₈ : Xα.t ⟶ Yβ.t
  | X.a => Y.y
  | X.a₁ => Y.w
  | X.a₂ => Y.x
  | X.a₃ => Y.y
  | X.a₄ => Y.w
  | X.b => Y.w
  | X.c => Y.x
  | X.d => Y.m
  | X.d₁ => Y.l

def f₈' : Xα ⟶ Yβ := ⟨
  f₈,
  by
    constructor
    · exact fun _ _ ↦ Set.mem_univ _
    · funext x
      cases x <;> rfl
⟩
```

:::htmlDiv («class» := "compact")
Map 9:

(i) $`\bar{a} = y` satisfies $`\beta^5\bar{a} = \beta^2\bar{a}`

(ii) $`\bar{b} = w` satisfies $`\beta\bar{b} = \beta^2\bar{a}`

(iii) $`\bar{c} = z` satisfies $`\beta\bar{c} = \beta^3\bar{a}`

(iv) $`\bar{d} = l` satisfies $`\beta^2\bar{d} = \bar{d}`
:::

```savedLean
def f₉ : Xα.t ⟶ Yβ.t
  | X.a => Y.y
  | X.a₁ => Y.w
  | X.a₂ => Y.x
  | X.a₃ => Y.y
  | X.a₄ => Y.w
  | X.b => Y.w
  | X.c => Y.z
  | X.d => Y.l
  | X.d₁ => Y.m

def f₉' : Xα ⟶ Yβ := ⟨
  f₉,
  by
    constructor
    · exact fun _ _ ↦ Set.mem_univ _
    · funext x
      cases x <;> rfl
⟩
```

:::htmlDiv («class» := "compact")
Map 10:

(i) $`\bar{a} = y` satisfies $`\beta^5\bar{a} = \beta^2\bar{a}`

(ii) $`\bar{b} = w` satisfies $`\beta\bar{b} = \beta^2\bar{a}`

(iii) $`\bar{c} = z` satisfies $`\beta\bar{c} = \beta^3\bar{a}`

(iv) $`\bar{d} = m` satisfies $`\beta^2\bar{d} = \bar{d}`
:::

```savedLean
def f₁₀ : Xα.t ⟶ Yβ.t
  | X.a => Y.y
  | X.a₁ => Y.w
  | X.a₂ => Y.x
  | X.a₃ => Y.y
  | X.a₄ => Y.w
  | X.b => Y.w
  | X.c => Y.z
  | X.d => Y.m
  | X.d₁ => Y.l

def f₁₀' : Xα ⟶ Yβ := ⟨
  f₁₀,
  by
    constructor
    · exact fun _ _ ↦ Set.mem_univ _
    · funext x
      cases x <;> rfl
⟩
```

:::htmlDiv («class» := "compact")
Map 11:

(i) $`\bar{a} = z` satisfies $`\beta^5\bar{a} = \beta^2\bar{a}`

(ii) $`\bar{b} = y` satisfies $`\beta\bar{b} = \beta^2\bar{a}`

(iii) $`\bar{c} = w` satisfies $`\beta\bar{c} = \beta^3\bar{a}`

(iv) $`\bar{d} = l` satisfies $`\beta^2\bar{d} = \bar{d}`
:::

```savedLean
def f₁₁ : Xα.t ⟶ Yβ.t
  | X.a => Y.z
  | X.a₁ => Y.y
  | X.a₂ => Y.w
  | X.a₃ => Y.x
  | X.a₄ => Y.y
  | X.b => Y.y
  | X.c => Y.w
  | X.d => Y.l
  | X.d₁ => Y.m

def f₁₁' : Xα ⟶ Yβ := ⟨
  f₁₁,
  by
    constructor
    · exact fun _ _ ↦ Set.mem_univ _
    · funext x
      cases x <;> rfl
⟩
```

:::htmlDiv («class» := "compact")
Map 12:

(i) $`\bar{a} = z` satisfies $`\beta^5\bar{a} = \beta^2\bar{a}`

(ii) $`\bar{b} = y` satisfies $`\beta\bar{b} = \beta^2\bar{a}`

(iii) $`\bar{c} = w` satisfies $`\beta\bar{c} = \beta^3\bar{a}`

(iv) $`\bar{d} = m` satisfies $`\beta^2\bar{d} = \bar{d}`
:::

```savedLean
def f₁₂ : Xα.t ⟶ Yβ.t
  | X.a => Y.z
  | X.a₁ => Y.y
  | X.a₂ => Y.w
  | X.a₃ => Y.x
  | X.a₄ => Y.y
  | X.b => Y.y
  | X.c => Y.w
  | X.d => Y.m
  | X.d₁ => Y.l

def f₁₂' : Xα ⟶ Yβ := ⟨
  f₁₂,
  by
    constructor
    · exact fun _ _ ↦ Set.mem_univ _
    · funext x
      cases x <;> rfl
⟩
```

```savedLean -show
end Ex15_7
```
::::

:::question (questionTitle := "Exercise 9") (questionPage := "185")
Our procedure treated $`X^{↻\alpha}` and  $`Y^{↻\beta}` very differently. Suppose that in addition to a presentation of $`X^{↻\alpha}` you had a presentation of $`Y^{↻\beta}`. Try to find a method to calculate the solutions of the equations $`(\bar{\mathbf{R}})` without having to draw the picture of $`Y^{↻\beta}`, but just working with a presentation. One can even program a computer to find all the maps $`f`, starting from presentations of $`X^{↻\alpha}` and $`Y^{↻\beta}`.
:::

:::::solution (solutionTo := "Exercise 9")
A presentation of $`Y^{↻\beta}` is given below.

:::htmlDiv («class» := "compact")
$`(\mathbf{L})`

$`l, \beta l, p, \beta p, \beta^2 p, \beta^3 p, \beta^4 p, \beta^5 p, q, z, \beta z, \beta^2 z, \beta^3 z`
:::

::::htmlDiv («class» := "vspace-above")
:::htmlDiv («class» := "compact")
$`(\mathbf{R})`

(i) $`\beta^2 l = l`

(ii) $`\beta^6 p = \beta^2 p`

(iii) $`\beta q = \beta p`

(iv) $`\beta^4 z = \beta z`
:::
::::
:::::

:::question (questionTitle := "Exercise 10") (questionPage := "186")
Find a presentation for this system, which continues to the right forever.
:::

:::::solution (solutionTo := "Exercise 10")
Let $`\alpha` be the endomap, and label the generators from top to bottom as $`a`, $`b`, and $`c`. Then a presentation is given below.

:::htmlDiv («class» := "compact")
$`(\mathbf{L})`

$`a, \alpha a, \alpha^2 a, \ldots, b, c, \alpha c`
:::

::::htmlDiv («class» := "vspace-above")
:::htmlDiv («class» := "compact")
$`(\mathbf{R})`

(i) $`\alpha b = \alpha a`

(ii) $`\alpha^2 c = \alpha^2 a`
:::
::::
:::::

:::question (questionTitle := "Exercise 12") (questionPage := "186")
A non-autonomous dynamical system $`S` is one in which the 'rule of evolution' $`{\mathbb{N} \times S \xrightarrow{r} S}` itself depends on time. These can be studied by reducing to the ordinary, or autonomous, system on the state space $`{X = \mathbb{N} \times S}` with dynamics given by $`{\rho(n, s) = \langle n+1, r(n, s) \rangle}`. Show that for any $`r` there is exactly one sequence $`u` in $`S` for which $`{u(n+1) = r(n, u(n))}` and for which $`{u(0) = s_0}` is a given starting point. (Hint: Reduce this to the universal property of $`{\mathbb{N} = (\mathbb{N}, \sigma)}` in 𝑺↻.)
:::

:::solution (solutionTo := "Exercise 12")
```savedComment
Exercise 15.12 (p. 186)
```

{htmlSpan (class := "todo")}[TODO Exercise 15.12]
:::

```savedLean -show
end CM
```
