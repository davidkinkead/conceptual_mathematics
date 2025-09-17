import VersoManual
import ConceptualMathematics.Meta.Lean
import ConceptualMathematics.Article1
import ConceptualMathematics.Session03
import ConceptualMathematics.Article2
import Mathlib

open Verso.Genre Manual InlineLean
open ConceptualMathematics
open CategoryTheory


#doc (Manual) "Session 4: Division of maps: Isomorphisms" =>

```savedImport
import ConceptualMathematics.Article1
import ConceptualMathematics.Session03
import ConceptualMathematics.Article2
import Mathlib
open CategoryTheory
```

```savedLean (show := false)
namespace CM
local notation:80 g " ⊚ " f:80 => CategoryStruct.comp f g
```

:::definition (definitionTerm := "Isomorphism") (definitionPage := "61")
If $`{A \xrightarrow{f} B}`, an _inverse for_ $`f` is a map $`{B \xrightarrow{g} A}` satisfying both
$$`g \circ f = 1_A \quad\text{and}\quad f \circ g = 1_B.`
If $`f` has an inverse, we say that $`f` is an _isomorphism_ or _invertible map_.
:::

See the original presentation of this definition of isomorphism at the beginning of Article II.

:::theoremDirective (theoremTitle := "Theorem (uniqueness of inverses)") (theoremPage := "61")
Any map $`f` has at most one inverse.
:::

:::proof (proofPage := "61")
Say $`{A \xrightarrow{f} B}`, and suppose that both $`{B \xrightarrow{g} A}` and $`{B \xrightarrow{h} A}` are inverses for $`f`; so
$$`g \circ f = 1_A \quad\text{and}\quad f \circ g = 1_B,\\\
h \circ f = 1_A \quad\text{and}\quad f \circ h = 1_B.`
We only need two of these equations to prove that $`g` and $`h` are the same:
$$`g = 1_A \circ g = (h \circ f) \circ g = h \circ (f \circ g) = h \circ 1_B = h.`
:::

See the Lean implementation `uniqueness_of_inverses` under the original presentation of this theorem in Article II.

In some of the Exercises that follow, we start to make use of mathlib's implementation of the `Category` class (see the definition of category at the end of Article I) ahead of our more extensive reliance on it in later Articles and Sessions.

:::question (questionTitle := "Exercise 1") (questionPage := "66")
Finish checking that $`d` is an isomorphism in our category by showing that $`{h \circ d}` and $`{d \circ h}` are indeed identity maps.
:::

:::solution (solutionTo := "Exercise 1")
```savedComment
Exercise 4.1 (p. 66)
```

To begin tackling this Exercise, we first define an abstract algebraic object as a type equipped with a carrier set and a 'combining-rule', which operates on elements of the carrier set (and which has the closure property).

```savedLean
structure AlgebraicObj where
  t : Type
  carrier : Set t
  oper : t → t → t
  oper_mem {a b} : a ∈ carrier → b ∈ carrier → oper a b ∈ carrier
```

Next we register a `Category` instance for our algebraic object, defining maps/morphisms between algebraic objects as morphisms between their underlying types that map elements of the domain carrier set to elements of the codomain carrier set and that respect the combining-rules.

```savedLean
instance : Category AlgebraicObj where
  Hom X Y := {
    f : X.t ⟶ Y.t //
    -- maps to codomain
    (∀ x ∈ X.carrier, f x ∈ Y.carrier)
    -- respects combining-rules
    ∧ (∀ x₁ ∈ X.carrier, ∀ x₂ ∈ X.carrier,
        f (X.oper x₁ x₂) = Y.oper (f x₁) (f x₂))
  }
  id := by
    intro X
    exact ⟨
      𝟙 X.t,
      by
        constructor
        · intro _ hx
          exact hx
        · intros
          rfl
    ⟩
  comp := by
    rintro _ _ _ ⟨f, hf⟩ ⟨g, hg⟩
    exact ⟨
      g ⊚ f,
      by
        obtain ⟨hf_mtc, hf_comb⟩ := hf
        obtain ⟨hg_mtc, hg_comb⟩ := hg
        constructor
        · intro x hx
          exact hg_mtc (f x) (hf_mtc x hx)
        · intro x₁ hx₁ x₂ hx₂
          dsimp
          have h₁ := hf_comb x₁ hx₁ x₂ hx₂
          rw [h₁]
          have h₂ :=
            hg_comb (f x₁) (hf_mtc x₁ hx₁) (f x₂) (hf_mtc x₂ hx₂)
          rw [h₂]
    ⟩
```

Lastly we define the concrete algebraic object of real numbers with addition as the combining-rule.

```savedLean
def RealAdd : AlgebraicObj := {
  t := ℝ
  carrier := Set.univ
  oper := (· + ·)
  oper_mem := fun _ _ ↦ Set.mem_univ _
}
```

We are now ready to complete the Exercise by defining $`d` and $`h` as morphisms in our category and showing that they are inverses.

```savedLean (show := false)
namespace Ex4_1
```

```savedLean
def d : RealAdd ⟶ RealAdd := ⟨
  fun (x : ℝ) ↦ 2 * x,
  by
    constructor
    · exact fun _ _ ↦ Set.mem_univ _
    · intros
      dsimp [RealAdd]
      ring
⟩

noncomputable def h : RealAdd ⟶ RealAdd := ⟨
  fun (x : ℝ) ↦ x / 2,
  by
    constructor
    · exact fun _ _ ↦ Set.mem_univ _
    · intros
      dsimp [RealAdd]
      ring
⟩

example : IsIso d := {
  out := by
    use h
    constructor
    · show h ⊚ d = 𝟙 RealAdd
      have h₀ : h.val ∘ d.val = id := by
        funext x
        dsimp [d, h, RealAdd]
        ring
      exact Subtype.eq h₀
    · show d ⊚ h = 𝟙 RealAdd
      have h₀ : d.val ∘ h.val = id := by
        funext x
        dsimp [d, h, RealAdd]
        ring
      exact Subtype.eq h₀
}
```

```savedLean (show := false)
end Ex4_1
```
:::

:::question (questionTitle := "Exercise 2") (questionPage := "66")
Find an isomorphism
$$`(\{\textit{odd}, \textit{even}\}, +) \xrightarrow{f} (\{\textit{positive}, \textit{negative}\}, \times).`
Hint: There are only two invertible maps of sets from $`{\{\textit{odd}, \textit{even}\}}` to $`{\{\textit{pos.}, \textit{neg.}\}}`. One of them 'respects the combining rules', but the other doesn't.
:::

:::solution (solutionTo := "Exercise 2")
```savedComment
Exercise 4.2 (p. 66)
```

For this Exercise, we continue to use the category of algebraic objects we defined in Exercise 1.

```savedLean (show := false)
namespace Ex4_2
```

Define addition for parity and multiplication for sign, and allow use of `+` and `*` notation.

```savedLean
inductive Parity where
  | odd | even

def add : Parity → Parity → Parity
  | Parity.odd, Parity.odd => Parity.even
  | Parity.odd, Parity.even => Parity.odd
  | Parity.even, Parity.odd => Parity.odd
  | Parity.even, Parity.even => Parity.even

instance : Add Parity where
  add := add

inductive Sign where
  | pos | neg

def mul : Sign → Sign → Sign
  | Sign.pos, Sign.pos => Sign.pos
  | Sign.pos, Sign.neg => Sign.neg
  | Sign.neg, Sign.pos => Sign.neg
  | Sign.neg, Sign.neg => Sign.pos

instance : Mul Sign where
  mul := mul
```

Create algebraic objects for parity with addition and sign with multiplication.

```savedLean
def parityAdd : AlgebraicObj := {
  t := Parity
  carrier := Set.univ
  oper := (· + ·)
  oper_mem := fun _ _ ↦ Set.mem_univ _
}

def signMul : AlgebraicObj := {
  t := Sign
  carrier := Set.univ
  oper := (· * ·)
  oper_mem := fun _ _ ↦ Set.mem_univ _
}
```

Propose a map $`f` from parity to sign, and its inverse, and form the corresponding morphisms between algebraic objects.

```savedLean
def f' : Parity ⟶ Sign
  | Parity.odd => Sign.neg
  | Parity.even => Sign.pos

def finv' : Sign ⟶ Parity
  | Sign.pos => Parity.even
  | Sign.neg => Parity.odd

def f : parityAdd ⟶ signMul := ⟨
  f',
  by
    constructor
    · exact fun _ _ ↦ Set.mem_univ _
    · intro a _ b _
      cases a <;> cases b <;> rfl
⟩

def finv : signMul ⟶ parityAdd := ⟨
  finv',
  by
    constructor
    · exact fun _ _ ↦ Set.mem_univ _
    · intro a _ b _
      cases a <;> cases b <;> rfl
⟩
```

Give a proof that our proposed map $`f` is indeed an isomorphism.

```savedLean
example : IsIso f := {
  out := by
    use finv
    constructor
    · have h₀ : finv.val ∘ f.val = id := by
        funext x
        cases x <;> rfl
      exact Subtype.eq h₀
    · have h₀ : f.val ∘ finv.val = id := by
        funext x
        cases x <;> rfl
      exact Subtype.eq h₀
}
```

```savedLean (show := false)
end Ex4_2
```
:::

:::question (questionTitle := "Exercise 3") (questionPage := "66")
An unscrupulous importer has sold to the algebraic category section of our zoo some creatures which are _not_ isomorphisms. Unmask the impostors.

(a) $`{(\mathbb{R}, +) \xrightarrow{p} (\mathbb{R}, +)}` by 'plus 1': $`{p\:x = x + 1}`.

(b) $`{(\mathbb{R}, \times) \xrightarrow{\mathit{sq}} (\mathbb{R}, \times)}` by 'squaring': $`{\mathit{sq}\:x = x^2}`.

(c) $`{(\mathbb{R}, \times) \xrightarrow{\mathit{sq}} (\mathbb{R}_{\ge 0}, \times)}` by 'squaring': $`{\mathit{sq}\:x = x^2}`.

(d) $`{(\mathbb{R}, +) \xrightarrow{m} (\mathbb{R}, +)}` by 'minus': $`{m\:x = -x}`.

(e) $`{(\mathbb{R}, \times) \xrightarrow{m} (\mathbb{R}, \times)}` by 'minus': $`{m\:x = -x}`.

(f) $`{(\mathbb{R}, \times) \xrightarrow{c} (\mathbb{R}_{>0}, \times)}` by 'cubing': $`{c\:x = x^3}`.

Hints: Exactly one is genuine. Some of the cruder impostors fail to be maps in our category, i.e. don't respect the combining-rules. The crudest is not even a map of _sets_ with the indicated domain and codomain.
:::

:::solution (solutionTo := "Exercise 3")
```savedComment
Exercise 4.3 (p. 66)
```

For clarity of presentation here, we restrict our use of the category of algebraic objects we defined in Exercise 1 to the one genuine case of (d).

(a) $`p` fails to respect the combining-rules.

```savedLean
example {p : ℝ ⟶ ℝ} (hp : ∀ x : ℝ, p x = x + 1)
    : ¬(∀ a b : ℝ, p (a + b) = p a + p b) := by
  push_neg
  use 0, 0
  rw [add_zero, ne_eq, left_eq_add, hp]
  norm_num
```

(b) $`\mathit{sq}` has no retraction.

```savedLean
example {sq : ℝ ⟶ ℝ} (hsq : ∀ x : ℝ, sq x = x ^ 2)
    : ¬(∃ r : ℝ → ℝ, (∀ x : ℝ, r (sq x) = x)) := by
  by_contra h
  obtain ⟨r, h⟩ := h
  have hpos : r (sq 1) = 1 := h 1
  have hneg : r (sq (-1)) = -1 := h (-1)
  rw [hsq] at hpos hneg
  rw [neg_sq, hpos] at hneg
  norm_num at hneg
```

(c) $`\mathit{sq}` has no retraction.

```savedLean
open NNReal in
example {sq : ℝ ⟶ ℝ≥0} (hsq : ∀ x : ℝ, sq x = x ^ 2)
    : ¬(∃ r : ℝ → ℝ, (∀ x : ℝ, r (sq x) = x)) := by
  by_contra h
  obtain ⟨r, h⟩ := h
  have hpos : r (sq 1) = 1 := h 1
  have hneg : r (sq (-1)) = -1 := h (-1)
  rw [hsq] at hpos hneg
  rw [neg_sq, hpos] at hneg
  norm_num at hneg
```

(d) is genuine.

```savedLean (show := false)
namespace Ex4_3_d
```

```savedLean
def m : RealAdd ⟶ RealAdd := ⟨
  fun (x : ℝ) ↦ -x,
  by
    constructor
    · exact fun _ _ ↦ Set.mem_univ _
    · intros
      dsimp [RealAdd]
      ring
⟩

def minv := m

example : IsIso m := {
  out := by
    use minv
    constructor
    · have h₀ : minv.val ∘ m.val = id := by
        funext x
        dsimp [m, minv]
        ring
      exact Subtype.eq h₀
    · have h₀ : m.val ∘ minv.val = id := by
        funext x
        dsimp [m, minv]
        ring
      exact Subtype.eq h₀
}
```

```savedLean (show := false)
end Ex4_3_d
```

(e) $`m` fails to respect the combining-rules.

```savedLean
example {m : ℝ ⟶ ℝ} (hm : ∀ x : ℝ, m x = -x)
    : ¬(∀ a b : ℝ, m (a * b) = m a * m b) := by
  push_neg
  use 1, 1
  rw [mul_one, ne_eq, hm]
  norm_num
```

(f) $`c` has an invalid codomain.

```savedLean (show := false)
namespace Ex4_3_f
```

```savedLean
abbrev ℝpos := { x : ℝ // x > 0 }

example {c : ℝ → ℝpos} (hc : ∀ x : ℝ, c x = x ^ 3)
    : ∃ x : ℝ, ¬(∃ y : ℝpos, y.val = c x) := by
  push_neg
  use -1
  rw [hc]
  norm_num
  intros
  linarith
```

```savedLean (show := false)
end Ex4_3_f
```
:::

```savedLean (show := false)
end CM
```
