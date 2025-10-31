import VersoManual
import ConceptualMathematics.Meta.Lean
import ConceptualMathematics.Article1
import ConceptualMathematics.Session02
import ConceptualMathematics.Session03
import Mathlib

open Verso.Genre Manual InlineLean
open ConceptualMathematics
open CategoryTheory


#doc (Manual) "Article II: Isomorphisms" =>

%%%
htmlSplit := .never
number := false
%%%

```savedImport
import ConceptualMathematics.Article1
import ConceptualMathematics.Session02
import ConceptualMathematics.Session03
import Mathlib
open CategoryTheory
```

```savedLean -show
namespace CM
local notation:80 g " ⊚ " f:80 => CategoryStruct.comp f g
```

# 1. Isomorphisms

:::definition (definitionTerm := "Isomorphism, Inverse") (definitionPage := "40")
A map $`{A \xrightarrow{f} B}` is called an _isomorphism_, or _invertible map_, if there is a map $`{B \xrightarrow{g} A}` for which $`{g \circ f = 1_A}` and $`{f \circ g = 1_B}`.

A map $`g` related to $`f` by satisfying these equations is called an _inverse for_ $`f`.

Two objects $`A` and $`B` are said to be _isomorphic_ if there is at least one isomorphism $`{A \xrightarrow{f} B}`.
:::

The corresponding mathlib definition for isomorphism is `Iso` (and `IsIso`), which we print below for reference.

```lean (name := out_Iso)
#print Iso
```

```leanOutput out_Iso
structure CategoryTheory.Iso.{v, u} {C : Type u} [Category.{v, u} C] (X Y : C) : Type v
number of parameters: 4
fields:
  CategoryTheory.Iso.hom : X ⟶ Y
  CategoryTheory.Iso.inv : Y ⟶ X
  CategoryTheory.Iso.hom_inv_id : self.inv ⊚ self.hom = 𝟙 X := by
    cat_disch
  CategoryTheory.Iso.inv_hom_id : self.hom ⊚ self.inv = 𝟙 Y := by
    cat_disch
constructor:
  CategoryTheory.Iso.mk.{v, u} {C : Type u} [Category.{v, u} C] {X Y : C} (hom : X ⟶ Y) (inv : Y ⟶ X)
    (hom_inv_id : inv ⊚ hom = 𝟙 X := by cat_disch) (inv_hom_id : hom ⊚ inv = 𝟙 Y := by cat_disch) : X ≅ Y
```

```lean (name := out_IsIso)
#print IsIso
```

```leanOutput out_IsIso
class CategoryTheory.IsIso.{v, u} {C : Type u} [Category.{v, u} C] {X Y : C} (f : X ⟶ Y) : Prop
number of parameters: 5
fields:
  CategoryTheory.IsIso.out : ∃ inv, inv ⊚ f = 𝟙 X ∧ f ⊚ inv = 𝟙 Y
constructor:
  CategoryTheory.IsIso.mk.{v, u} {C : Type u} [Category.{v, u} C] {X Y : C} {f : X ⟶ Y}
    (out : ∃ inv, inv ⊚ f = 𝟙 X ∧ f ⊚ inv = 𝟙 Y) : IsIso f
```

:::excerpt (excerptPage := "41")
_Reflexive_: $`A` is isomorphic to $`A`.

_Symmetric_: If $`A` is isomorphic to $`B`, then $`B` is isomorphic to $`A`.

_Transitive_: If $`A` is isomorphic to $`B`, and $`B` is isomorphic to $`C`, then $`A` is isomorphic to $`C`.
:::

The respective mathlib definitions are `Iso.refl`, `Iso.symm`, and `Iso.trans`, which we print below for reference.

```lean (name := out_Iso_refl)
#print Iso.refl
```

```leanOutput out_Iso_refl
def CategoryTheory.Iso.refl.{v, u} : {C : Type u} → [inst : Category.{v, u} C] → (X : C) → X ≅ X :=
fun {C} [Category.{v, u} C] X ↦ { hom := 𝟙 X, inv := 𝟙 X, hom_inv_id := ⋯, inv_hom_id := ⋯ }
```

```lean (name := out_Iso_symm)
#print Iso.symm
```

```leanOutput out_Iso_symm
def CategoryTheory.Iso.symm.{v, u} : {C : Type u} → [inst : Category.{v, u} C] → {X Y : C} → (X ≅ Y) → (Y ≅ X) :=
fun {C} [Category.{v, u} C] {X Y} I ↦ { hom := I.inv, inv := I.hom, hom_inv_id := ⋯, inv_hom_id := ⋯ }
```

```lean (name := out_Iso_trans)
#print Iso.trans
```

```leanOutput out_Iso_trans
def CategoryTheory.Iso.trans.{v, u} : {C : Type u} →
  [inst : Category.{v, u} C] → {X Y Z : C} → (X ≅ Y) → (Y ≅ Z) → (X ≅ Z) :=
fun {C} [Category.{v, u} C] {X Y Z} α β ↦
  { hom := β.hom ⊚ α.hom, inv := α.inv ⊚ β.inv, hom_inv_id := ⋯, inv_hom_id := ⋯ }
```

:::question (questionTitle := "Exercise 1") (questionPage := "41")
(R) Show that $`{A \xrightarrow{1_A} A}` is an isomorphism. (Hint: find an inverse for $`1_A`.)

(S) Show that if $`{A \xrightarrow{f} B}` is an isomorphism, and $`{B \xrightarrow{g} A}` is an inverse for $`f`; then $`g` is also an isomorphism. (Hint: find an inverse for $`g`.)

(T) Show that if $`{A \xrightarrow{f} B}` and $`{B \xrightarrow{k} C}` are isomorphisms, $`{A \xrightarrow{k \circ f} C}` is also an isomorphism.
:::

:::solution (solutionTo := "Exercise 1")
```savedComment
Exercise II.1 (p. 41)
```

```savedLean -show
namespace ExII_1
```

```savedLean
variable {𝒞 : Type u} [Category.{v, u} 𝒞] {A B C : 𝒞}
```

(R) $`1_A` is an inverse for itself, so $`1_A` is an isomorphism.

```savedLean
example : IsIso (𝟙 A) := by
  use 𝟙 A
  constructor <;> exact Category.id_comp (𝟙 A)
```

(S) $`f` is an inverse for $`g`, so $`g` is an isomorphism. (Note that the hypothesis "$`f` is an isomorphism" is redundant here and could be omitted.)

```savedLean
example (f : A ⟶ B) (_ : IsIso f)
    (g : B ⟶ A) (hg : g ⊚ f = 𝟙 A ∧ f ⊚ g = 𝟙 B)
    : IsIso g := by
  use f
  exact ⟨hg.2, hg.1⟩
```

(T) Composition of isomorphisms is transitive, so $`{k \circ f}` is an isomorphism.

```savedLean
example (f : A ⟶ B) (hf : IsIso f) (k : B ⟶ C) (hk : IsIso k)
    : IsIso (k ⊚ f) := by
  obtain ⟨finv, hfinv⟩ := hf
  obtain ⟨kinv, hkinv⟩ := hk
  use finv ⊚ kinv
  constructor
  · rw [Category.assoc, ← Category.assoc k]
    rw [hkinv.1, Category.id_comp, hfinv.1]
  · rw [Category.assoc, ← Category.assoc finv]
    rw [hfinv.2, Category.id_comp, hkinv.2]
```

```savedLean -show
end ExII_1
```
:::

:::question (questionTitle := "Exercise 2") (questionPage := "42")
Suppose $`{B \xrightarrow{g} A}` and $`{B \xrightarrow{k} A}` are _both_ inverses for $`{A \xrightarrow{f} B}`. Show that $`{g = k}`.
:::

:::solution (solutionTo := "Exercise 2")
```savedComment
Exercise II.2 (p. 42)
```

The inverse of a map is unique (when it exists).

```savedLean
example {𝒞 : Type u} [Category.{v, u} 𝒞] {A B : 𝒞} (f : A ⟶ B)
    (g : B ⟶ A) (hg : g ⊚ f = 𝟙 A ∧ f ⊚ g = 𝟙 B)
    (k : B ⟶ A) (hk : k ⊚ f = 𝟙 A ∧ f ⊚ k = 𝟙 B)
    : g = k := by
  calc
    g = 𝟙 A ⊚ g := by rw [Category.comp_id]
    _ = (k ⊚ f) ⊚ g := by rw [hk.1]
    _ = k ⊚ (f ⊚ g) := by rw [Category.assoc]
    _ = k ⊚ 𝟙 B := by rw [hg.2]
    _ = k := by rw [Category.id_comp]
```
:::

:::question (questionTitle := "Exercise 3") (questionPage := "43")
_If $`f` has an inverse_, then $`f` satisfies the two cancellation laws:

(a) If $`{f \circ h = f \circ k}`, then $`{h = k}`.

(b) If $`{h \circ f = k \circ f}`, then $`{h = k}`.

_Warning_: The following 'cancellation law' is _not_ correct, even if $`f` has an inverse.

(c) (wrong): If $`{h \circ f = f \circ k}`, then $`{h = k}`.
:::

:::solution (solutionTo := "Exercise 3")
```savedComment
Exercise II.3 (p. 43)
```

```savedLean -show
namespace ExII_3
```

```savedLean
variable {𝒞 : Type u} [Category.{v, u} 𝒞] {A B : 𝒞}
```

(a) We show that $`f` is left-cancellative.

```savedLean
example (f : A ⟶ B)
    (hf : ∃ finv : B ⟶ A, finv ⊚ f = 𝟙 A ∧ f ⊚ finv = 𝟙 B)
    (h : B ⟶ A) (k : B ⟶ A)
    : f ⊚ h = f ⊚ k → h = k := by
  obtain ⟨finv, hfinv₁, hfinv₂⟩ := hf
  intro h₁
  have h₂ : finv ⊚ f ⊚ h = finv ⊚ f ⊚ k := by rw [h₁]
  repeat rw [Category.assoc] at h₂
  rw [hfinv₁] at h₂
  repeat rw [Category.comp_id] at h₂
  exact h₂
```

(b) We show that $`f` is right-cancellative.

```savedLean
example (f : A ⟶ B)
    (hf : ∃ finv : B ⟶ A, finv ⊚ f = 𝟙 A ∧ f ⊚ finv = 𝟙 B)
    (h : B ⟶ A) (k : B ⟶ A)
    : h ⊚ f = k ⊚ f → h = k := by
  obtain ⟨finv, hfinv₁, hfinv₂⟩ := hf
  intro h₁
  have h₂ : (h ⊚ f) ⊚ finv = (k ⊚ f) ⊚ finv := by rw [h₁]
  repeat rw [← Category.assoc] at h₂
  rw [hfinv₂] at h₂
  repeat rw [Category.id_comp] at h₂
  exact h₂
```

(c) We take our counterexample from endomaps on `Fin 2`, the canonical type with two elements.

```savedLean
def f : Fin 2 ⟶ Fin 2
  | 0 => 1
  | 1 => 0
```

$`f` has an inverse, as required. ($`f` is self-inverse.)

```savedLean
example : f ⊚ f = 𝟙 (Fin 2) := by
  funext x
  fin_cases x <;> dsimp [f]

def h : Fin 2 ⟶ Fin 2
  | 0 => 1
  | 1 => 1

def k : Fin 2 ⟶ Fin 2
  | 0 => 0
  | 1 => 0

example : ¬(h ⊚ f = f ⊚ k → h = k) := by
  push_neg
  constructor
  · funext x
    fin_cases x <;> dsimp [f, h, k]
  · by_contra h₀
    have h₁ : h 0 = 1 := rfl
    have h₂ : k 0 = 0 := rfl
    rw [← h₀, h₁] at h₂
    norm_num at h₂
```

```savedLean -show
end ExII_3
```
:::

:::question (questionTitle := "Exercise 4") (questionPage := "44")
For each of the five maps below: decide whether it is invertible; and if it is invertible, find a 'formula' for the inverse map.

1. $`\mathbb{R} \xrightarrow{f} \mathbb{R},\; f(x) = 3x + 7`
2. $`\mathbb{R}_{\ge 0} \xrightarrow{g} \mathbb{R}_{\ge 0},\; g(x) = x^2`
3. $`\mathbb{R} \xrightarrow{h} \mathbb{R},\; h(x) = x^2`
4. $`\mathbb{R} \xrightarrow{k} \mathbb{R}_{\ge 0},\; k(x) = x^2`
5. $`\mathbb{R}_{\ge 0} \xrightarrow{l} \mathbb{R}_{\ge 0},\; l(x) = \dfrac{1}{x + 1}`
:::

:::solution (solutionTo := "Exercise 4")
```savedComment
Exercise II.4 (p. 44)
```

Since all five maps have their domain and codomain as the real numbers (or a subset of the real numbers), we implement them as functions in Lean.

$`f` is invertible, with inverse $`{f^{-1}(x) = \dfrac{x - 7}{3}}`.

```savedLean
example (f : ℝ → ℝ) (hf : ∀ x : ℝ, f x = 3 * x + 7)
    : ∃ finv : ℝ → ℝ, finv ∘ f = id ∧ f ∘ finv = id := by
  use fun x ↦ (x - 7) / 3 -- f⁻¹(x)
  constructor
  · funext x
    rw [Function.comp_apply, id_eq, hf x]
    ring
  · funext x
    rw [Function.comp_apply, id_eq, hf ((x - 7) / 3)]
    ring
```

$`g` is invertible, with inverse $`{g^{-1}(x) = \sqrt{x}}`.

```savedLean
open NNReal in
example (g : ℝ≥0 → ℝ≥0) (hg : ∀ x : ℝ≥0, g x = x * x)
  : ∃ ginv : ℝ≥0 → ℝ≥0, ginv ∘ g = id ∧ g ∘ ginv = id := by
  use fun x ↦ NNReal.sqrt x -- g⁻¹(x)
  constructor
  · funext x
    rw [Function.comp_apply, id_eq, hg x]
    exact NNReal.sqrt_mul_self x
  · funext x
    rw [Function.comp_apply, id_eq, hg (sqrt x)]
    exact mul_self_sqrt x
```

$`h` is not invertible, since $`{h(1) = h(-1) = 1}`.

```savedLean
example (h : ℝ → ℝ) (hh : ∀ x : ℝ, h x = x * x)
    : ¬(∃ hinv : ℝ → ℝ, hinv ∘ h = id ∧ h ∘ hinv = id) := by
  push_neg
  intro hinv h_inv_left _
  have h₁ : h 1 = 1 := by
    rw [hh 1]
    norm_num
  have h₂ : h (-1) = 1 := by
    rw [hh (-1)]
    norm_num
  have h₃ : (hinv ∘ h) 1 = 1:= by
    rw [h_inv_left, id_eq]
  have h₄ : (hinv ∘ h) (-1) = -1 := by
    rw [h_inv_left, id_eq]
  dsimp at h₃ h₄
  rw [h₁] at h₃
  rw [h₂] at h₄
  linarith
```

$`k` is not invertible, since $`{k(1) = k(-1) = 1}`.

```savedLean
open NNReal in
example (k : ℝ → ℝ≥0) (hk : ∀ x : ℝ, k x = x * x)
    : ¬(∃ kinv : ℝ≥0 → ℝ, kinv ∘ k = id ∧ k ∘ kinv = id) := by
  push_neg
  intro kinv h_inv_left _
  have h₁ : k 1 = 1 := by
    rw [← coe_eq_one, hk 1]
    norm_num
  have h₂ : k (-1) = 1 := by
    rw [← coe_eq_one, hk (-1)]
    norm_num
  have h₃ : (kinv ∘ k) 1 = 1:= by
    rw [h_inv_left, id_eq]
  have h₄ : (kinv ∘ k) (-1) = -1 := by
    rw [h_inv_left, id_eq]
  dsimp at h₃ h₄
  rw [h₁] at h₃
  rw [h₂] at h₄
  linarith
```

$`l` is invertible, with inverse $`{l^{-1}(x) = \dfrac{1}{x} - 1}`, provided that we restrict the codomain of $`l` to the interval $`{(0,1]}`.

{htmlSpan (class := "todo")}[TODO Exercise II.4.5]
:::

# 2. General division problems: Determination and choice

Exercise 5 concerns counting the number of _sections_ and _retractions_ for a map (though those terms aren't formally defined until a short while later on p. 49). Rather than providing an exhaustive list of maps, we introduce here two formulas — what the book later calls _Chad's formula_ and _Danilo's formula_ (p. 117).

The former states that the number of sections for a map $`p` is given by
$$`\prod_{\mathbf{1} \xrightarrow{a} A} \#(p^{-1}a),`
where $`A` is the codomain of $`p`.

```savedComment
Chad's formula
```

```savedLean
def Chad's_formula {α χ : Type*} [DecidableEq α]
    [Fintype α] [Fintype χ] (X : Finset χ) (A : Finset α)
    (p : χ → α)
    : ℕ :=
  ∏ a ∈ A, pinvCount a
where
  pinvCount (a : α) : ℕ := X.filter (fun x ↦ p x = a) |>.card
```

The latter states that the number of retractions for a map $`j`, assuming $`j` is injective, is given by
$$`(\#A)^{(\#X - \#A)},`
where $`A` is the domain of $`j` and $`X` is the codomain of $`j`.

```savedComment
Danilo's formula
```

```savedLean
open Finset in
def Danilo's_formula {α χ : Type*}
    [Fintype α] [Fintype χ] (A : Finset α) (X : Finset χ)
    (j : α → χ) (p : χ → α) (_ : p ∘ j = id) (_ : Function.Injective j)
    : ℕ :=
  #A ^ (#X - #A)
```

:::question (questionTitle := "Exercise 5") (questionPage := "47")
Given

$`\{b, p, q, r, s\} \xrightarrow{g} \{0, 1\}\\\
\qquad b \mapsto 0\\\
\qquad p \mapsto 0\\\
\qquad q \mapsto 0\\\
\qquad r \mapsto 1\\\
\qquad s \mapsto 1,`

how many maps $`f` are there with $`{g \circ f = 1_{\{0, 1\}}}`?

Choosing a particular such $`f`, how many maps $`g` (including the given one) satisfy the same equation?
:::

:::solution (solutionTo := "Exercise 5")
```savedComment
Exercise II.5 (p. 47)
```

```savedLean -show
namespace ExII_5
```

```savedLean
inductive XElems where
  | b | p | q | r | s
  deriving Fintype

def A : Finset (Fin 2) := Finset.univ
def X : Finset XElems := Finset.univ

open XElems in
def g : XElems → Fin 2
  | b => 0
  | p => 0
  | q => 0
  | r => 1
  | s => 1
```

By Chad's formula, we have 6 different maps $`f` with $`{g \circ f = 1_{\{0, 1\}}}`.

```savedLean (name := outII_5_1)
#eval Chad's_formula X A g
```

```leanOutput outII_5_1
6
```

We choose $`f` to be

```savedLean
open XElems in
def f : Fin 2 → XElems
  | 0 => b
  | 1 => r
```

Then, by Danilo's formula, we have $`{(\#A)^{(\#X - \#A)} = 2^3 = 8}` different maps $`g`.

```savedLean (name := outII_5_2)
#eval Danilo's_formula A X f g
  (by funext x; fin_cases x <;> rfl)
  (by intro x y _; fin_cases x <;> fin_cases y <;>
    (first | rfl | simp; trivial))
```

```leanOutput outII_5_2
8
```

```savedLean -show
end ExII_5
```
:::

# 3. Retractions, sections, and idempotents

:::definition (definitionTerm := "Retraction, Section") (definitionPage := "49")
If $`{A \xrightarrow{f} B}`:

a _retraction for_ $`f` is a map $`{B \xrightarrow{r} A}` for which $`{r \circ f = 1_A}`;

a _section for_ $`f` is a map $`{B \xrightarrow{s} A}` for which $`{f \circ s = 1_B}`.
:::

The mathlib definition corresponding to _retraction_ is `SplitMono` (and `IsSplitMono`), which we print below for reference.

```lean (name := out_SplitMono)
#print SplitMono
```

```leanOutput out_SplitMono
structure CategoryTheory.SplitMono.{v₁, u₁} {C : Type u₁} [Category.{v₁, u₁} C] {X Y : C} (f : X ⟶ Y) : Type v₁
number of parameters: 5
fields:
  CategoryTheory.SplitMono.retraction : Y ⟶ X
  CategoryTheory.SplitMono.id : self.retraction ⊚ f = 𝟙 X := by
    cat_disch
constructor:
  CategoryTheory.SplitMono.mk.{v₁, u₁} {C : Type u₁} [Category.{v₁, u₁} C] {X Y : C} {f : X ⟶ Y} (retraction : Y ⟶ X)
    (id : retraction ⊚ f = 𝟙 X := by cat_disch) : SplitMono f
```

```lean (name := out_IsSplitMono)
#print IsSplitMono
```

```leanOutput out_IsSplitMono
class CategoryTheory.IsSplitMono.{v₁, u₁} {C : Type u₁} [Category.{v₁, u₁} C] {X Y : C} (f : X ⟶ Y) : Prop
number of parameters: 5
fields:
  CategoryTheory.IsSplitMono.exists_splitMono : Nonempty (SplitMono f)
constructor:
  CategoryTheory.IsSplitMono.mk.{v₁, u₁} {C : Type u₁} [Category.{v₁, u₁} C] {X Y : C} {f : X ⟶ Y}
    (exists_splitMono : Nonempty (SplitMono f)) : IsSplitMono f
```

We alias `SplitMono` and `IsSplitMono` as `Retraction` and `IsRetraction`, respectively, to remain aligned with the terminology in the book.

```savedComment
Retraction, IsRetraction
```

```savedLean
abbrev Retraction {𝒞 : Type u} [Category.{v, u} 𝒞] {A B : 𝒞}
    (f : A ⟶ B) :=
  SplitMono f
abbrev IsRetraction {𝒞 : Type u} [Category.{v, u} 𝒞] {A B : 𝒞}
    (f : A ⟶ B) :=
  IsSplitMono f
```

The mathlib definition corresponding to _section_ is `SplitEpi` (and `IsSplitEpi`), which we print below for reference.

```lean (name := out_SplitEpi)
#print SplitEpi
```

```leanOutput out_SplitEpi
structure CategoryTheory.SplitEpi.{v₁, u₁} {C : Type u₁} [Category.{v₁, u₁} C] {X Y : C} (f : X ⟶ Y) : Type v₁
number of parameters: 5
fields:
  CategoryTheory.SplitEpi.section_ : Y ⟶ X
  CategoryTheory.SplitEpi.id : f ⊚ self.section_ = 𝟙 Y := by
    cat_disch
constructor:
  CategoryTheory.SplitEpi.mk.{v₁, u₁} {C : Type u₁} [Category.{v₁, u₁} C] {X Y : C} {f : X ⟶ Y} (section_ : Y ⟶ X)
    (id : f ⊚ section_ = 𝟙 Y := by cat_disch) : SplitEpi f
```

```lean (name := out_IsSplitEpi)
#print IsSplitEpi
```

```leanOutput out_IsSplitEpi
class CategoryTheory.IsSplitEpi.{v₁, u₁} {C : Type u₁} [Category.{v₁, u₁} C] {X Y : C} (f : X ⟶ Y) : Prop
number of parameters: 5
fields:
  CategoryTheory.IsSplitEpi.exists_splitEpi : Nonempty (SplitEpi f)
constructor:
  CategoryTheory.IsSplitEpi.mk.{v₁, u₁} {C : Type u₁} [Category.{v₁, u₁} C] {X Y : C} {f : X ⟶ Y}
    (exists_splitEpi : Nonempty (SplitEpi f)) : IsSplitEpi f
```

We alias `SplitEpi` and `IsSplitEpi` as `Section` and `IsSection`, respectively, to remain aligned with the terminology in the book.

```savedComment
Section, IsSection
```

```savedLean
abbrev Section {𝒞 : Type u} [Category.{v, u} 𝒞] {A B : 𝒞}
    (f : A ⟶ B) :=
  SplitEpi f
abbrev IsSection {𝒞 : Type u} [Category.{v, u} 𝒞] {A B : 𝒞}
    (f : A ⟶ B) :=
  IsSplitEpi f
```

:::theoremDirective (theoremTitle := "Proposition 1") (theoremPage := "51")
If a map $`{A \xrightarrow{f} B}` has a section, then for any $`T` and for any map $`{T \xrightarrow{y} B}` there exists a map $`{T \xrightarrow{x} A}` for which $`{f \circ x = y}`.
:::

:::proof (proofPage := "51")
The assumption means that we have a map $`s` for which $`{f \circ s = 1_B}`. Thus for any given map $`{T \xrightarrow{y} B}` we see that we could define a map $`x` with at least the correct domain and codomain by taking the composite $`s` following $`y`
$$`x = s \circ y.`
Does this map $`x` actually satisfy the required equation? Calculating
$$`f \circ x = f \circ (s \circ y) = (f \circ s) \circ y = 1_B \circ y = y`
we see that it does.
:::

Our implementation in Lean faithfully follows the argument of the book proof given above.

```savedComment
Proposition 1 (p. 51)
```

```savedLean
theorem prop1 {𝒞 : Type u} [Category.{v, u} 𝒞] {A B T : 𝒞}
    (f : A ⟶ B) [hf : IsSection f]
    : ∀ y : T ⟶ B, ∃ x : T ⟶ A, f ⊚ x = y := by
  obtain ⟨s, hf⟩ := hf
  intro y
  use s ⊚ y
  rw [Category.assoc]
  rw [hf]
  exact Category.comp_id y
```

:::question (questionTitle := "Exercise 6") (questionPage := "52")
If the map $`{A \xrightarrow{f} B}` has a retraction, then for any map $`{A \xrightarrow{g} T}`, there is a map $`{B \xrightarrow{t} T}` for which $`{t \circ f = g}`. (This is Proposition 1\*.)
:::

:::solution (solutionTo := "Exercise 6")
```savedComment
Exercise II.6 (Proposition 1*) (p. 52)
```

Put $`{t = g \circ r}`.

```savedLean
theorem «prop1*» {𝒞 : Type u} [Category.{v, u} 𝒞] {A B T : 𝒞}
    (f : A ⟶ B) [hf : IsRetraction f]
    : ∀ g : A ⟶ T, ∃ t : B ⟶ T, t ⊚ f = g := by
  obtain ⟨r, hf⟩ := hf
  intro g
  use g ⊚ r
  rw [← Category.assoc, hf, Category.id_comp]
```
:::

:::theoremDirective (theoremTitle := "Proposition 2") (theoremPage := "52")
Suppose a map $`{A \xrightarrow{f} B}` has a retraction. Then for any set $`T` and for any pair of maps $`{T \xrightarrow{x_1} A}`, $`{T \xrightarrow{x_2} A}` from any set $`T` to $`A`
$$`\text{if}\; f \circ x_1 = f \circ x_2 \;\text{then}\; x_1 = x_2.`
:::

:::proof (proofPage := "52")
Looking back at the definition, we see that the assumption means that we have a map $`r` for which $`{r \circ f = 1_A}`. Using the assumption that $`x_1` and $`x_2` are such that $`f` composes with them to get the same $`{T \rightarrow B}`, we can compose further with $`r` as follows:
$$`x_1 = 1_A \circ x_1 = (r \circ f) \circ x_1 = r \circ (f \circ x_1) = r \circ (f \circ x_2) = (r \circ f) \circ x_2 = 1_A \circ x_2 = x_2.`
:::

Our implementation in Lean generalises the proposition from sets to any categorical object but otherwise faithfully follows the argument of the book proof given above.

```savedComment
Proposition 2 (p. 52)
```

```savedLean
theorem prop2 {𝒞 : Type u} [Category.{v, u} 𝒞] {A B T : 𝒞}
    (f : A ⟶ B) [hf : IsRetraction f]
    : ∀ x₁ x₂ : T ⟶ A, f ⊚ x₁ = f ⊚ x₂ → x₁ = x₂ := by
  obtain ⟨r, hf⟩ := hf
  intro x₁ x₂ h
  rw [← Category.comp_id x₁]
  rw [← hf]
  rw [← Category.assoc]
  rw [h]
  rw [Category.assoc]
  rw [hf]
  exact Category.comp_id x₂
```

:::definition (definitionTerm := "Injective, Monomorphism") (definitionPage := "52")
A map $`f` satisfying the conclusion of Proposition 2 (for any pair of maps $`{T \xrightarrow{x_1} A}` and $`{T \xrightarrow{x_2} A}`, if $`{f \circ x_1 = f \circ x_2}` then $`{x_1 = x_2}`) is said to be _injective for maps from_ $`T`.

If $`f` is injective for maps from $`T` for every $`T`, one says that $`f` is _injective_, or is a _monomorphism_.
:::

The corresponding mathlib definition is `Mono`, which we print below for reference.

```lean (name := out_Mono)
#print Mono
```

```leanOutput out_Mono
class CategoryTheory.Mono.{v, u} {C : Type u} [Category.{v, u} C] {X Y : C} (f : X ⟶ Y) : Prop
number of parameters: 5
fields:
  CategoryTheory.Mono.right_cancellation : ∀ {Z : C} (g h : Z ⟶ X), f ⊚ g = f ⊚ h → g = h
constructor:
  CategoryTheory.Mono.mk.{v, u} {C : Type u} [Category.{v, u} C] {X Y : C} {f : X ⟶ Y}
    (right_cancellation : ∀ {Z : C} (g h : Z ⟶ X), f ⊚ g = f ⊚ h → g = h) : Mono f
```

:::question (questionTitle := "Exercise 7") (questionPage := "53")
Suppose the map $`{A \xrightarrow{f} B}` has a section. Then for any set $`T` and any pair $`{B \xrightarrow{t_1} T}`, $`{B \xrightarrow{t_2} T}` of maps from $`B` to $`T`, if $`{t_1 \circ f = t_2 \circ f}` then $`{t_1 = t_2}`. (This is Proposition 2\*.)
:::

:::solution (solutionTo := "Exercise 7")
```savedComment
Exercise II.7 (Proposition 2*) (p. 53)
```

A proof of Proposition 2\* is given below.

```savedLean
theorem «prop2*» {𝒞 : Type u} [Category.{v, u} 𝒞] {A B T : 𝒞}
    (f : A ⟶ B) [hf : IsSection f]
    : ∀ t₁ t₂ : B ⟶ T, t₁ ⊚ f = t₂ ⊚ f → t₁ = t₂ := by
  obtain ⟨s, hf⟩ := hf
  intro t₁ t₂ h
  rw [← Category.id_comp t₁, ← hf]
  rw [Category.assoc, h, ← Category.assoc]
  rw [hf, Category.id_comp]
```
:::

:::definition (definitionTerm := "Surjective, Epimorphism") (definitionPage := "53")
A map $`f` with this cancellation property (if $`{t_1 \circ f = t_2 \circ f}` then $`{t_1 = t_2}`) for every $`T` is called an _epimorphism_.
:::

The corresponding mathlib definition is `Epi`, which we print below for reference.

```lean (name := out_Epi)
#print Epi
```

```leanOutput out_Epi
class CategoryTheory.Epi.{v, u} {C : Type u} [Category.{v, u} C] {X Y : C} (f : X ⟶ Y) : Prop
number of parameters: 5
fields:
  CategoryTheory.Epi.left_cancellation : ∀ {Z : C} (g h : Y ⟶ Z), g ⊚ f = h ⊚ f → g = h
constructor:
  CategoryTheory.Epi.mk.{v, u} {C : Type u} [Category.{v, u} C] {X Y : C} {f : X ⟶ Y}
    (left_cancellation : ∀ {Z : C} (g h : Y ⟶ Z), g ⊚ f = h ⊚ f → g = h) : Epi f
```

:::excerpt (excerptPage := "53")
Thus both 'monomorphism' and 'epimorphism' are 'cancellation' properties.
:::

The mathlib theorems `cancel_mono` and `cancel_epi` are relevant here.

```savedComment
cancel_mono, cancel_epi
```

```savedLean
example {𝒞 : Type u} [Category.{v, u} 𝒞] {X Y Z : 𝒞}
    (f : X ⟶ Y) [Mono f] {g h : Z ⟶ X}
    : f ⊚ g = f ⊚ h ↔ g = h := cancel_mono f

example {𝒞 : Type u} [Category.{v, u} 𝒞] {X Y Z : 𝒞}
    (f : X ⟶ Y) [Epi f] {g h : Y ⟶ Z}
    : g ⊚ f = h ⊚ f ↔ g = h := cancel_epi f
```

:::theoremDirective (theoremTitle := "Proposition 3") (theoremPage := "53")
If $`{A \xrightarrow{f} B}` has a retraction and if $`{B \xrightarrow{g} C}` has a retraction, then $`{A \xrightarrow{g \circ f} C}` has a retraction.
:::

:::proof (proofPage := "53")
Let $`{r_1 \circ f = 1_A}` and $`{r_2 \circ g = 1_B}`. Then a good guess for a retraction of the composite would be the composite of the retractions _in the opposite order_ (which is anyway the only order in which they can be composed). Does it in fact work?
$$`r \circ (g \circ f) = (r_1 \circ r_2) \circ (g \circ f) = r_1 \circ (r_2 \circ g) \circ f = r_1 \circ 1_B \circ f = r_1 \circ f = 1_A`
proves that $`r` is a retraction for $`{g \circ f}`.
:::

Our implementation in Lean faithfully follows the argument of the book proof given above.

```savedComment
Proposition 3 (p. 53)
```

```savedLean
theorem prop3 {𝒞 : Type u} [Category.{v, u} 𝒞] {A B C : 𝒞}
    (f : A ⟶ B) [hf : IsRetraction f] (g : B ⟶ C) [hg : IsRetraction g]
    : IsRetraction (g ⊚ f) := by
  obtain ⟨r₁, hf⟩ := hf
  obtain ⟨r₂, hg⟩ := hg
  use r₁ ⊚ r₂
  change (r₁ ⊚ r₂) ⊚ (g ⊚ f) = 𝟙 A
  rw [Category.assoc, ← Category.assoc g]
  rw [hg]
  rw [Category.id_comp]
  exact hf
```

We note that the corresponding mathlib instance is `instIsSplitMonoComp`.

```savedComment
instIsSplitMonoComp
```

```savedLean
example {𝒞 : Type u} [Category.{v, u} 𝒞] {A B C : 𝒞}
    (f : A ⟶ B) [hf : IsRetraction f] (g : B ⟶ C) [hg : IsRetraction g]
    : IsRetraction (g ⊚ f) := instIsSplitMonoComp
```

:::question (questionTitle := "Exercise 8") (questionPage := "54")
Prove that the composite of two maps, each having sections, has itself a section.
:::

:::solution (solutionTo := "Exercise 8")
```savedComment
Exercise II.8 (p. 54)
```

The section of the composite is the composite of the sections in the opposite order (cf. Proposition 3).

```savedLean
example {𝒞 : Type u} [Category.{v, u} 𝒞] {A B C : 𝒞}
    (f : A ⟶ B) [hf : IsSection f] (g : B ⟶ C) [hg : IsSection g]
    : IsSection (g ⊚ f) := by
  obtain ⟨s₁, hf⟩ := hf
  obtain ⟨s₂, hg⟩ := hg
  use s₁ ⊚ s₂
  change (g ⊚ f) ⊚ (s₁ ⊚ s₂) = 𝟙 C
  rw [Category.assoc, ← Category.assoc s₁]
  rw [hf]
  rw [Category.id_comp]
  exact hg
```
:::

We note that the corresponding mathlib instance is `instIsSplitEpiComp`.

```savedComment
instIsSplitEpiComp
```

```savedLean
example {𝒞 : Type u} [Category.{v, u} 𝒞] {A B C : 𝒞}
    (f : A ⟶ B) [hf : IsSection f] (g : B ⟶ C) [hg : IsSection g]
    : IsSection (g ⊚ f) := instIsSplitEpiComp
```

:::definition (definitionTerm := "Idempotent") (definitionPage := "54")
An endomap $`e` is called _idempotent_ if $`{e \circ e = e}`.
:::

We implement `Idempotent` and `IsIdempotent` in Lean as follows:

```savedComment
Idempotent, IsIdempotent
```

```savedLean
structure Idempotent {𝒞 : Type u} [Category.{v, u} 𝒞] (A : 𝒞) where
  e : A ⟶ A
  idem : e ⊚ e = e

class IsIdempotent {𝒞 : Type u} [Category.{v, u} 𝒞] {A : 𝒞}
    (e : A ⟶ A) where
  idem : e ⊚ e = e
```

:::question (questionTitle := "Exercise 9") (questionPage := "54")
Suppose $`r` is a retraction of $`f` (equivalently $`f` is a section of $`r`) and let $`{e = f \circ r}`. Show that $`e` is an idempotent.... Show that if $`f` is an isomorphism, then $`e` is the identity.
:::

:::solution (solutionTo := "Exercise 9")
```savedComment
Exercise II.9 (p. 54)
```

```savedLean -show
namespace ExII_9
```

```savedLean
variable {𝒞 : Type u} [Category.{v, u} 𝒞] {A B : 𝒞}
         (f : A ⟶ B) (e : B ⟶ B)
```

We show that $`e` is an idempotent.

```savedLean
example (r : Retraction f) (he : e = f ⊚ r.retraction)
    : IsIdempotent e := {
  idem := by
    rw [he, Category.assoc, ← Category.assoc f, r.id,
        Category.id_comp]
}
```

We show that $`e` is the identity if $`f` is an isomorphism.

```savedLean
example [hf : IsIso f]
    (r : Retraction f) (he : e = f ⊚ r.retraction)
    : e = 𝟙 B := by
  have ⟨finv, hfinv⟩ := hf
  rw [← hfinv.2, ← Category.id_comp f, ← r.id]
  repeat rw [← Category.assoc]
  rwa [hfinv.2, Category.id_comp]
```

```savedLean -show
end ExII_9
```
:::

:::theoremDirective (theoremTitle := "Theorem (uniqueness of inverses)") (theoremPage := "54")
If $`f` has both a retraction $`r` and a section $`s` then $`{r = s}`.
:::

:::proof (proofPage := "54")
From the definition we have, if $`{A \xrightarrow{f} B}`, both of the equations
$$`r \circ f = 1_A \quad\text{and}\quad f \circ s = 1_B.`
Then by the identity laws and the associative law
$$`r = r \circ 1_B = r \circ (f \circ s) = (r \circ f) \circ s = 1_A \circ s = s.`
:::

Our implementation in Lean faithfully follows the argument of the book proof given above.

```savedComment
Theorem (uniqueness of inverses) (p. 54)
```

```savedLean
theorem uniqueness_of_inverses {𝒞 : Type u} [Category.{v, u} 𝒞]
    {A B : 𝒞} (f : A ⟶ B) (r : Retraction f) (s : Section f)
    : r.retraction = s.section_ := by
  obtain ⟨r, hr⟩ := r
  obtain ⟨s, hs⟩ := s
  change r = s
  calc
    r = r ⊚ 𝟙 B := by rw [Category.id_comp]
    _ = r ⊚ (f ⊚ s) := by rw [hs]
    _ = (r ⊚ f) ⊚ s := by rw [← Category.assoc]
    _ = 𝟙 A ⊚ s := by rw [← hr]
    _ = s := Category.comp_id s
```

# 4. Isomorphisms and automorphisms

:::definition (definitionTerm := "Isomorphism, Inverse") (definitionPage := "54")
A map $`{A \xrightarrow{f} B}` is called an _isomorphism_ if there exists another map $`{B \xrightarrow{f^{-1}} A}` which is both a retraction and a section for $`f`:
$$`f \circ f⁻¹ = 1_B,\\\
f⁻¹ \circ f = 1_A.`
Such a map $`f^{-1}` is called _the inverse map for_ $`f`; since both of the two equations are required, the theorem of uniqueness of inverses shows that there is only one inverse.
:::

We compare these definitions of _isomorphism_ and _inverse_ with the earlier definitions on p. 40. A proof that the two definitions of isomorphism are equivalent is given below.

```savedComment
Equivalency of two definitions of isomorphism (pp. 54 & 40)
```

```savedLean
example {𝒞 : Type u} [Category.{v, u} 𝒞] {A B : 𝒞}
    (f : A ⟶ B) (r : Retraction f) (s : Section f)
    : r.retraction = s.section_ ↔ IsIso f := by
  constructor
  · intro h
    exact {
      out := by
        use r.retraction
        constructor
        · exact r.id
        · rw [h]
          exact s.id
    }
  · rintro ⟨finv, hfinv⟩
    obtain ⟨r, hr⟩ := r
    obtain ⟨s, hs⟩ := s
    change r = s
    calc
      r = r ⊚ 𝟙 B := by rw [Category.id_comp]
      _ = r ⊚ (f ⊚ s) := by rw [hs]
      _ = (r ⊚ f) ⊚ s := by rw [← Category.assoc]
      _ = 𝟙 A ⊚ s := by rw [← hr]
      _ = s := Category.comp_id s
```

When working with inverse maps in Excercise 10, we make use of mathlib's `CategoryTheory.inv`, which we print below for reference.

```lean (name := out_CategoryTheory_inv)
#print CategoryTheory.inv
```

```leanOutput out_CategoryTheory_inv
def CategoryTheory.inv.{v, u} : {C : Type u} →
  [inst : Category.{v, u} C] → {X Y : C} → (f : X ⟶ Y) → [I : IsIso f] → Y ⟶ X :=
fun {C} [Category.{v, u} C] {X Y} f [IsIso f] ↦ Classical.choose ⋯
```

:::question (questionTitle := "Exercise 10") (questionPage := "55")
If $`{A \xrightarrow{f} B \xrightarrow{g} C}` are both isomorphisms, then $`{g \circ f}` is an isomorphism too, and $`{(g \circ f)^{-1} = f^{-1} \circ g^{-1}}`.
:::

:::solution (solutionTo := "Exercise 10")
```savedComment
Exercise II.10 (p. 55)
```

The inverse of the composite is the composite of the inverses in the opposite order.

```savedLean
open CategoryTheory in
example {𝒞 : Type u} [Category.{v, u} 𝒞] {A B C : 𝒞}
    (f : A ⟶ B) [hf : IsIso f] (g : B ⟶ C) [hg : IsIso g]
    : IsIso (g ⊚ f) ∧ inv (g ⊚ f) = inv f ⊚ inv g := by
  constructor
  · obtain ⟨finv, hfinv⟩ := hf
    obtain ⟨ginv, hginv⟩ := hg
    exact {
      out := by
        use finv ⊚ ginv
        constructor
        · rw [Category.assoc, ← Category.assoc g]
          rw [hginv.1]
          rw [Category.id_comp]
          exact hfinv.1
        · rw [Category.assoc, ← Category.assoc finv]
          rw [hfinv.2]
          rw [Category.id_comp]
          exact hginv.2
    }
  · exact IsIso.inv_comp
```
:::

:::question (questionTitle := "Exercise 11") (questionPage := "55")
If $`{A = \{\mathit{Fatima}, \mathit{Omer}, \mathit{Alysia}\}}` and $`{B = \{\mathit{coffee}, \mathit{tea}, \mathit{cocoa}\}}`, find an example of an isomorphism $`{A \xrightarrow{f} B}`. If $`{C = \{\mathit{true}, \mathit{false}\}}`, can you find any isomorphism $`{A \rightarrow C}`?
:::

:::solution (solutionTo := "Exercise 11")
```savedComment
Exercise II.11 (p. 55)
```

```savedLean
namespace ExII_11
```

For convenience, we use finite types here instead of finite sets.

```savedLean
inductive A where
  | Fatima | Omer | Alysia
  deriving Fintype

inductive B where
  | coffee | tea | cocoa
  deriving Fintype
```

We give a map $`f` and its inverse $`f^{-1}` below, along with a proof that $`f` is an isomorphism.

```savedLean
def f : A ⟶ B
  | A.Fatima => B.coffee
  | A.Omer => B.tea
  | A.Alysia => B.cocoa

def finv : B ⟶ A
  | B.coffee => A.Fatima
  | B.tea => A.Omer
  | B.cocoa => A.Alysia

example : IsIso f := {
  out := by
    use finv
    constructor
    all_goals (
      funext x
      fin_cases x <;> dsimp [f, finv]
    )
}

end ExII_11
```

Since $`{\#A > \#C}`, there can be no pair $`{A \xrightarrow{j} C}`, $`{C \xrightarrow{p} A}` such that $`{p \circ j = 1_A}`; hence there is no isomorphism $`{A \rightarrow C}`.
:::

:::excerpt (excerptPage := "55")
A map which is both an endomap and at the same time an isomorphism is usually called by the one word _automorphism_.
:::

The corresponding mathlib definition is `Aut`, which we print below for reference.

```lean (name := out_Aut)
#print Aut
```

```leanOutput out_Aut
def CategoryTheory.Aut.{v, u} : {C : Type u} → [Category.{v, u} C] → C → Type v :=
fun {C} [Category.{v, u} C] X ↦ X ≅ X
```

Compare this to the mathlib definition `End` for endomorphisms of an object in a category.

```lean (name := out_End)
#print End
```

```leanOutput out_End
def CategoryTheory.End.{v, u} : {C : Type u} → [CategoryStruct.{v, u} C] → C → Type v :=
fun {C} [CategoryStruct.{v, u} C] X ↦ X ⟶ X
```

:::question (questionTitle := "Exercise 12") (questionPage := "56")
How many isomorphisms are there from $`{A = \{\mathit{Fatima}, \mathit{Omer}, \mathit{Alysia}\}}` to $`{B = \{\mathit{coffee}, \mathit{tea}, \mathit{cocoa}\}}`? How many automorphisms of $`A` are there? The answers should be less than 27 — why?
:::

:::solution (solutionTo := "Exercise 12")
```savedComment
Exercise II.12 (p. 56), isoCount, autCount
```

Provided two sets/types have the same number $`n` of elements, the number of isomorphisms between them is $`n!`; if the sets/types have different numbers of elements, then there are no isomorphisms between them. We implement this formula in Lean as follows:

```savedLean
def isoCount (α β : Type*) [Fintype α] [Fintype β] : ℕ :=
  if Fintype.card α = Fintype.card β then
    Nat.factorial (Fintype.card α)
  else
    0
```

By the formula above, we have 6 different isomorphisms.

```savedLean (name := outII_12_1)
open ExII_11

#eval isoCount A B
```

```leanOutput outII_12_1
6
```

Essentially the same formula applies to automorphisms, since an automorphism is just an isomorphism from a set/type to itself. Thus, there are also 6 different automorphisms of $`A`.

```savedLean
abbrev autCount (α : Type*) [Fintype α] := isoCount α α
```

```savedLean (name := outII_12_2)
open ExII_11

#eval autCount A
```

```leanOutput outII_12_2
6
```

By Alysia's formula, $`{3^3 = 27}` is the number of distinct maps $`{A \rightarrow B}` (or $`{A \rightarrow A}`), so the number of isomorphisms between $`A` and $`B` (or automorphisms of $`A`) must be less than 27.
:::

:::excerpt (excerptPage := "57")
An automorphism in the category of sets is also traditionally called a _permutation_, suggesting that it shifts the elements of its set around in a specified way.
:::

Repeating the second part of Exercise 12, now using sets instead of types, we have

```savedComment
permCount
```

```savedLean
def permCount {α : Type*} (s : Finset α) : ℕ :=
  if 0 < Finset.card s then
    Nat.factorial (Finset.card s)
  else
    0
```

```savedLean (name := out_permCount)
open ExII_11

#eval permCount (Finset.univ (α := A))
```

```leanOutput out_permCount
6
```

```savedLean -show
end CM
```
