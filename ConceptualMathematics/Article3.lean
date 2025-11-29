import VersoManual
import ConceptualMathematics.Meta.Lean
import ConceptualMathematics.Article2
import ConceptualMathematics.Review
import Mathlib

open Verso.Genre Manual InlineLean
open ConceptualMathematics
open CategoryTheory


#doc (Manual) "Article III: Examples of categories" =>

%%%
htmlSplit := .never
number := false
%%%

```savedImport
import ConceptualMathematics.Article2
import ConceptualMathematics.Review
import Mathlib
open CategoryTheory
```

```savedLean -show
namespace CM
local notation:80 g " ⊚ " f:80 => CategoryStruct.comp f g
```

# 1. The category 𝑺↻ of endomaps of sets

*The category 𝑺↻ of endomaps of sets* is described on pp. 136–137. We implement this category in Lean in a similar way to the category of algebraic objects that we developed in the solution to Session 4, Exercise 1. Our Lean implementation follows closely the definition of _category_ given on p. 21, so we reproduce that definition here, interspersed with our comments (italicised) and the corresponding Lean code.

```savedComment
The (concrete) category 𝑺↻ of endomaps of sets (pp. 136–137)
```

:::definition (definitionTerm := "Category") (definitionPage := "21")
A _category_ consists of the DATA:

\(1\) OBJECTS

_An object in the category 𝑺↻ is a set equipped with an endomap._

```savedLean
structure SetWithEndomap where
  t : Type
  carrier : Set t
  toEnd : t ⟶ t
  toEnd_mem {a} : a ∈ carrier → toEnd a ∈ carrier
```

\(2\) MAPS

_A map in the category 𝑺↻ is one which respects the given structure — i.e., a morphism which commutes. Note that we use a Lean subtype here instead of a Lean structure._

```savedLean
def SetWithEndomapHom (X Y : SetWithEndomap) := {
  f : X.t ⟶ Y.t //
      (∀ x ∈ X.carrier, f x ∈ Y.carrier) -- maps to codomain
      ∧ f ⊚ X.toEnd = Y.toEnd ⊚ f -- commutes
}
```

\(3\) For each map $`f`, one object as DOMAIN of $`f` and one object as CODOMAIN of $`f`

_As given above, a `SetWithEndomapHom` is a subtype of morphisms between the underlying types of two `SetWithEndomap` objects, so the domain and codomain are already specified._

\(4\) For each object $`A` an IDENTITY MAP, which has domain $`A` and codomain $`A`

_We define the identity map within the `SetWithEndomapHom` namespace to facilitate code re-use in some closely related category instances that follow shortly._

```savedLean
def SetWithEndomapHom.id (X : SetWithEndomap)
    : SetWithEndomapHom X X := ⟨
  𝟙 X.t,
  by
    constructor
    · intro _ hx
      exact hx
    · rfl
⟩
```

\(5\) For each pair of maps $`{A \xrightarrow{f} B \xrightarrow{g} C}`, a COMPOSITE MAP map $`{A \xrightarrow{g \;\mathrm{following}\; f} C}`

_We likewise define composition of maps within the `SetWithEndomapHom` namespace._

```savedLean
def SetWithEndomapHom.comp {X Y Z : SetWithEndomap}
    (f : SetWithEndomapHom X Y) (g : SetWithEndomapHom Y Z)
    : SetWithEndomapHom X Z := ⟨
  g.val ⊚ f.val,
  by
    obtain ⟨hf_mtc, hf_comm⟩ := f.property
    obtain ⟨hg_mtc, hg_comm⟩ := g.property
    constructor
    · intro x hx
      exact hg_mtc (f.val x) (hf_mtc x hx)
    · rw [← Category.assoc, hf_comm, Category.assoc, hg_comm,
          ← Category.assoc]
⟩
```

_We can now instantiate the category 𝑺↻._

```savedLean
instance instCatSetWithEndomap : Category SetWithEndomap where
  Hom := SetWithEndomapHom
  id := SetWithEndomapHom.id
  comp := SetWithEndomapHom.comp
```

satisfying the following RULES:

\(i\) IDENTITY LAWS: If $`{A \xrightarrow{f} B}`, then $`{1_B \circ f = f}` and $`{f \circ 1_A = f}`

_The identity laws are given by the methods `Category.comp_id` and `Category.id_comp`, respectively, which Lean is able to discharge automatically using tactics._

\(ii\) ASSOCIATIVE LAW: If $`{A \xrightarrow{f} B \xrightarrow{g} C \xrightarrow{h} D}`, then $`{(h \circ g) \circ f = h \circ (g \circ f)}`

_The associative law is given by the method `Category.assoc`, which Lean is likewise able to discharge automatically._
:::

For good measure, we make the category 𝑺↻ a concrete category.

```savedLean
instance {X Y : SetWithEndomap}
    : FunLike (instCatSetWithEndomap.Hom X Y) X.t Y.t where
  coe f := f.val
  coe_injective' := fun _ _ h ↦ Subtype.eq h

instance
    : ConcreteCategory SetWithEndomap instCatSetWithEndomap.Hom where
  hom f := f
  ofHom f := f
```

:::question (questionTitle := "Exercise 1") (questionPage := "137")
Show that if both
$$`X^{↻\alpha} \xrightarrow{f} Y^{↻\beta}`
...and also
$$`Y^{↻\beta} \xrightarrow{g} Z^{↻\gamma}`
are maps in 𝑺↻, then the composite $`{g \circ f}` in 𝑺 actually defines another map in 𝑺↻. Hint: What should the domain and the codomain (in the sense of 𝑺↻) of this third map be? Transfer the definition (given for the case $`f`) to the cases $`g` and $`{g \circ f}`; then calculate that the equations satisfied by $`g` and $`f` imply the desired equation for $`{g \circ f}`.
:::

:::solution (solutionTo := "Exercise 1")
```savedComment
Exercise III.1 (p. 137)
```

Using only the category `Type`, we have

```savedLean
example {X Y Z : Type}
    (α : X ⟶ X) (β : Y ⟶ Y) (γ : Z ⟶ Z)
    (f : X ⟶ Y) (hf_comm : f ⊚ α = β ⊚ f)
    (g : Y ⟶ Z) (hg_comm : g ⊚ β = γ ⊚ g)
    : (g ⊚ f) ⊚ α = γ ⊚ (g ⊚ f) := by
  -- cf. SetWithEndomapHom.comp above
  rw [← Category.assoc, hf_comm, Category.assoc, hg_comm,
      ← Category.assoc]
```

Using instead our implementation of the category 𝑺↻ of endomaps of sets gives

```savedLean
example {X Y Z : SetWithEndomap} (f : X ⟶ Y) (g : Y ⟶ Z) : X ⟶ Z :=
  g ⊚ f
```
:::

# 3. Two subcategories of 𝑺↻

:::htmlDetails (classDetails := "") (classSummary := "") (summary := "We implement the category 𝑺ᵉ of idempotent endomaps of sets, described on p. 138. We re-use code from our earlier implementation of the category 𝑺↻.")
```savedComment
The (concrete) category 𝑺ᵉ of idempotent endomaps of sets (p. 138)
```

```savedLean
structure SetWithIdemEndomap extends SetWithEndomap where
  idem : toEnd ⊚ toEnd = toEnd

instance instCatSetWithIdemEndomap : Category SetWithIdemEndomap where
  Hom X Y := SetWithEndomapHom X.toSetWithEndomap Y.toSetWithEndomap
  id X := SetWithEndomapHom.id X.toSetWithEndomap
  comp := SetWithEndomapHom.comp

instance {X Y : SetWithIdemEndomap}
    : FunLike (instCatSetWithIdemEndomap.Hom X Y) X.t Y.t where
  coe f := f.val
  coe_injective' := fun _ _ h ↦ Subtype.eq h

instance
    : ConcreteCategory SetWithIdemEndomap instCatSetWithIdemEndomap.Hom
    where
  hom f := f
  ofHom f := f
```
:::

:::htmlDetails (classDetails := "") (classSummary := "") (summary := "We implement the category 𝑺◯ of invertible endomaps of sets (automorphisms of sets, permutations), described on p. 138.")
```savedComment
The (concrete) category 𝑺◯ of invertible endomaps of sets (p. 138)
```

```savedLean
structure SetWithInvEndomap extends SetWithEndomap where
  inv : ∃ inv, inv ⊚ toEnd = 𝟙 t ∧ toEnd ⊚ inv = 𝟙 t

instance instCatSetWithInvEndomap : Category SetWithInvEndomap where
  Hom X Y := SetWithEndomapHom X.toSetWithEndomap Y.toSetWithEndomap
  id X := SetWithEndomapHom.id X.toSetWithEndomap
  comp := SetWithEndomapHom.comp

instance {X Y : SetWithInvEndomap}
    : FunLike (instCatSetWithInvEndomap.Hom X Y) X.t Y.t where
  coe f := f.val
  coe_injective' := fun _ _ h ↦ Subtype.eq h

instance
    : ConcreteCategory SetWithInvEndomap instCatSetWithInvEndomap.Hom
    where
  hom f := f
  ofHom f := f
```
:::

# 4. Categories of endomaps

*The category 𝑪↻ of endomaps* is described on pp. 138–139. We implement the category 𝑪↻ below (cf. the category 𝑺↻).

```savedComment
The (concrete) category 𝑪↻ of endomaps (pp. 138–139)
```

Define the objects.

```savedLean
structure Endomap where
  carrier : Type
  toEnd : carrier ⟶ carrier
```

Define the maps.

```savedLean
def EndomapHom (X Y : Endomap) := {
  f : X.carrier ⟶ Y.carrier //
      f ⊚ X.toEnd = Y.toEnd ⊚ f -- commutes
}
```

Define the identity maps and the composite maps.

```savedLean
namespace EndomapHom

def id (X : Endomap) : EndomapHom X X := ⟨
  𝟙 X.carrier,
  rfl
⟩

def comp {X Y Z : Endomap}
    (f : EndomapHom X Y) (g : EndomapHom Y Z)
    : EndomapHom X Z := ⟨
  g.val ⊚ f.val,
  by
    obtain hf_comm := f.property
    obtain hg_comm := g.property
    rw [← Category.assoc, hf_comm, Category.assoc, hg_comm,
        ← Category.assoc]
⟩

end EndomapHom
```

Instantiate the category 𝑪↻.

```savedLean
instance instCatEndomap : Category Endomap where
  Hom := EndomapHom
  id := EndomapHom.id
  comp := EndomapHom.comp
```

Make the category 𝑪↻ a concrete category.

```savedLean
instance {X Y : Endomap}
    : FunLike (instCatEndomap.Hom X Y) X.carrier Y.carrier where
  coe f := f.val
  coe_injective' := fun _ _ h ↦ Subtype.eq h

instance : ConcreteCategory Endomap instCatEndomap.Hom where
  hom f := f
  ofHom f := f
```

:::htmlDetails (classDetails := "") (classSummary := "") (summary := "We implement the category 𝑪ᵉ of idempotents, described on pp. 138–139.")
```savedComment
The (concrete) category 𝑪ᵉ of idempotents (pp. 138–139)
```

```savedLean
structure IdemEndomap extends Endomap where
  idem : toEnd ⊚ toEnd = toEnd

instance instCatIdemEndomap : Category IdemEndomap where
  Hom X Y := EndomapHom X.toEndomap Y.toEndomap
  id X := EndomapHom.id X.toEndomap
  comp := EndomapHom.comp

instance {X Y : IdemEndomap}
    : FunLike (instCatIdemEndomap.Hom X Y) X.carrier Y.carrier where
  coe f := f.val
  coe_injective' := fun _ _ h ↦ Subtype.eq h

instance : ConcreteCategory IdemEndomap instCatIdemEndomap.Hom where
  hom f := f
  ofHom f := f
```
:::

:::htmlDetails (classDetails := "") (classSummary := "") (summary := "We implement the category 𝑪◯ of isomorphic endomaps (automorphisms), described on pp. 138–139.")
```savedComment
The (concrete) category 𝑪◯ of isomorphic endomaps (pp. 138–139)
```

```savedLean
structure InvEndomap extends Endomap where
  inv : ∃ inv, inv ⊚ toEnd = 𝟙 carrier ∧ toEnd ⊚ inv = 𝟙 carrier

instance instCatInvEndomap : Category InvEndomap where
  Hom X Y := EndomapHom X.toEndomap Y.toEndomap
  id X := EndomapHom.id X.toEndomap
  comp := EndomapHom.comp

instance {X Y : InvEndomap}
    : FunLike (instCatInvEndomap.Hom X Y) X.carrier Y.carrier where
  coe f := f.val
  coe_injective' := fun _ _ h ↦ Subtype.eq h

instance : ConcreteCategory InvEndomap instCatInvEndomap.Hom where
  hom f := f
  ofHom f := f
```
:::

:::htmlDetails (classDetails := "") (classSummary := "") (summary := "We implement the category 𝑪ᶿ of involutions, described on pp. 138–139.")
```savedComment
The (concrete) category 𝑪ᶿ of involutions (pp. 138–139)
```

```savedLean
structure InvolEndomap extends InvEndomap where
  invol : toEnd ⊚ toEnd = 𝟙 carrier

instance instCatInvolEndomap : Category InvolEndomap where
  Hom X Y := EndomapHom X.toEndomap Y.toEndomap
  id X := EndomapHom.id X.toEndomap
  comp := EndomapHom.comp

instance {X Y : InvolEndomap}
    : FunLike (instCatInvolEndomap.Hom X Y) X.carrier Y.carrier where
  coe f := f.val
  coe_injective' := fun _ _ h ↦ Subtype.eq h

instance : ConcreteCategory InvolEndomap instCatInvolEndomap.Hom where
  hom f := f
  ofHom f := f
```
:::

:::question (questionTitle := "Exercise 2") (questionPage := "139")
What can you prove about an idempotent which has a retraction?
:::

:::solution (solutionTo := "Exercise 2")
```savedComment
Exercise III.2 (p. 139)
```

We can prove that the only idempotent which has a retraction is the identity.

```savedLean
example {𝒞 : Type u} [Category.{v, u} 𝒞] {A : 𝒞} {α β : A ⟶ A}
    (h_idem : α ⊚ α = α) (h_retraction : β ⊚ α = 𝟙 A)
    : α = 𝟙 A := by
  calc
    α = 𝟙 A ⊚ α := by rw [Category.comp_id]
    _ = (β ⊚ α) ⊚ α := by rw [h_retraction]
    _ = β ⊚ α ⊚ α := by rw [Category.assoc]
    _ = β ⊚ α := by rw [h_idem]
    _ = 𝟙 A := by rw [h_retraction]
```
:::

:::question (questionTitle := "Exercise 3") (questionPage := "140")
A finite set $`A` has an even number of elements iff (i.e. if and only if) there is an involution on $`A` with _no fixed points_; $`A` has an odd number of elements iff there is an involution on $`A` with just _one_ fixed point. Here we rely on known ideas about numbers — but these properties can be used as a _definition_ of oddness or evenness that can be verified without counting if the structure of a real situation suggests an involution. The map 'mate of' in a group $`A` of socks is an obvious example.
:::

:::solution (solutionTo := "Exercise 3")
```savedComment
Exercise III.3 (p. 140)
```

{htmlSpan (class := "todo")}[TODO Exercise III.3]
:::

In Exercises 4–7 that follow, we use the type $`\mathbb{Z}` instead of the set $`\mathbb{Z}` (and hence the concrete category `Type` instead of the category 𝑺 of sets).

:::question (questionTitle := "Exercise 4") (questionPage := "140")
If $`{\alpha(x) = -x}` is considered as an endomap of $`\mathbb{Z}`, is $`\alpha` an involution or an idempotent? What are its fixed points?
:::

:::solution (solutionTo := "Exercise 4")
```savedComment
Exercise III.4 (p. 140)
```

```savedLean -show
namespace ExIII_4
```

Define the endomap $`{\alpha(x) = -x}` on $`\mathbb{Z}`.

```savedLean
def α : ℤ ⟶ ℤ := fun x ↦ -x
```

$`\alpha` is not an idempotent.

```savedLean
example : ¬(IsIdempotent α) := by
  by_contra h
  have h_contra : (α ⊚ α) 1 = α 1 := congrFun h.idem 1
  dsimp [α] at h_contra
  norm_num at h_contra
```

$`\alpha` is an involution.

```savedLean
example : IsInvolution α := {
  invol := by
    funext
    dsimp [CategoryStruct.comp, α]
    ring
}
```

The only fixed point of $`\alpha` is 0.

```savedLean
example {x : ℤ} : Function.IsFixedPt α x ↔ x = 0 := by
  dsimp [Function.IsFixedPt, α]
  constructor
  · exact eq_zero_of_neg_eq
  · intro hx
    rw [hx]
    exact neg_zero
```

Note that since the converse of `eq_zero_of_neg_eq` is true, we can also state the following:

```savedLean
theorem _root_.eq_zero_iff_neg_eq {α : Type u}
    [AddCommGroup α] [LinearOrder α] [IsOrderedAddMonoid α]
    {a : α} : -a = a ↔ a = 0 := by
  constructor
  · exact eq_zero_of_neg_eq
  · intro h
    rw [h]
    exact neg_zero
```

We can then use this new lemma to simplify the proof in the previous example.

```savedLean
example {x : ℤ} : Function.IsFixedPt α x ↔ x = 0 := eq_zero_iff_neg_eq
```

```savedLean -show
end ExIII_4
```
:::

:::question (questionTitle := "Exercise 5") (questionPage := "140")
Same questions as above, if instead $`{\alpha(x) = |x|}`, the absolute value.
:::

:::solution (solutionTo := "Exercise 5")
```savedComment
Exercise III.5 (p. 140)
```

```savedLean -show
namespace ExIII_5
```

Define the endomap $`{\alpha(x) = |x|}` on $`\mathbb{Z}`.

```savedLean
def α : ℤ ⟶ ℤ := fun x ↦ |x|
```

$`\alpha` is an idempotent.

```savedLean
example : IsIdempotent α := {
  idem := by
    funext
    dsimp [CategoryStruct.comp, α]
    rw [abs_abs]
}
```

$`\alpha` is not an involution.

```savedLean
example : ¬(IsInvolution α) := by
  by_contra h
  have h_contra : (α ⊚ α) (-1) = (𝟙 ℤ) (-1) := congrFun h.invol (-1)
  dsimp [α] at h_contra
  norm_num at h_contra
```

The fixed points of $`\alpha` are all the points greater than or equal to 0.

```savedLean
example {x : ℤ} : Function.IsFixedPt α x ↔ 0 ≤ x := by
  dsimp [Function.IsFixedPt, α]
  constructor
  · intro hx
    rw [← hx]
    exact abs_nonneg x
  · exact abs_of_nonneg
```

Note that since the converse of `abs_of_nonneg` is true with the additional assumption `[AddRightMono α]`, we can state the following:

```savedLean
theorem _root_.abs_iff_nonneg {α : Type u_1}
    [Lattice α] [AddGroup α]
    {a : α} [AddLeftMono α] [AddRightMono α] : 0 ≤ a ↔ |a| = a := by
  constructor
  · exact abs_of_nonneg
  · intro h
    rw [← h]
    exact abs_nonneg a
```

We can then use this new lemma to simplify the proof in the previous example.

```savedLean
example {x : ℤ} : Function.IsFixedPt α x ↔ 0 ≤ x := abs_iff_nonneg.symm
```

```savedLean -show
end ExIII_5
```
:::

:::question (questionTitle := "Exercise 6") (questionPage := "140")
If $`\alpha` is the endomap of $`\mathbb{Z}`, defined by the formula $`{\alpha(x) = x + 3}`, is $`\alpha` an automorphism? If so, write the formula for its inverse.
:::

:::solution (solutionTo := "Exercise 6")
```savedComment
Exercise III.6 (p. 140)
```

```savedLean -show
namespace ExIII_6
```

Define the endomap $`{\alpha(x) = x + 3}` on $`\mathbb{Z}`.

```savedLean
def α : ℤ ⟶ ℤ := fun x ↦ x + 3
```

$`\alpha` is an automorphism, with inverse $`{\alpha^{-1}(x) = x - 3}`.

```savedLean
example : IsIso α := by
  let αinv : ℤ ⟶ ℤ := fun x ↦ x - 3
  exact {
    out := by
      use αinv
      constructor
      all_goals
        funext
        dsimp [CategoryStruct.comp, α, αinv]
        ring
  }
```

```savedLean -show
end ExIII_6
```
:::

:::question (questionTitle := "Exercise 7") (questionPage := "140")
Same questions for $`{\alpha(x) = 5x}`.
:::

:::solution (solutionTo := "Exercise 7")
```savedComment
Exercise III.7 (p. 140)
```

```savedLean -show
namespace ExIII_7
```

Define the endomap $`{\alpha(x) = 5x}` on $`\mathbb{Z}`.

```savedLean
def α : ℤ ⟶ ℤ := fun x ↦ 5 * x
```

$`\alpha` is not an automorphism.

```savedLean
example : ¬(IsIso α) := by
  by_contra h
  obtain ⟨αinv, _, h_right_inv⟩ := h.out
  have h_contra₁ : (α ⊚ αinv) 1 = (𝟙 ℤ) 1 := congrFun h_right_inv 1
  have h_contra₂ : (5 : ℤ) ∣ 1 := by
    use αinv 1
    exact h_contra₁.symm
  norm_num at h_contra₂
```

```savedLean -show
end ExIII_7
```
:::

:::question (questionTitle := "Exercise 8") (questionPage := "140")
Show that both 𝑪ᵉ, 𝑪ᶿ are subcategories of the category \[whose objects are all the endomaps $`\alpha` in 𝑪 which satisfy $`{\alpha \circ \alpha \circ \alpha = \alpha}`\], i.e. that either an idempotent or an involution will satisfy $`{\alpha^3 = \alpha}`.
:::

:::solution (solutionTo := "Exercise 8")
```savedComment
Exercise III.8 (p. 140)
```

We show that the category 𝑪ᵉ of idempotents is a subcategory of the category given in the question.

```savedLean
example {α : IdemEndomap}
    : α.toEnd ⊚ α.toEnd ⊚ α.toEnd = α.toEnd := by
  repeat rw [α.idem]
```

Or, more generally, that an idempotent will satisfy $`{\alpha^3 = \alpha}`.

```savedLean
example {𝒞 : Type u} [Category.{v, u} 𝒞] {A : 𝒞}
    (α : A ⟶ A) [IsIdempotent α] : α ⊚ α ⊚ α = α := by
  repeat rw [IsIdempotent.idem]
```

We show that the category 𝑪ᶿ of involutions is a subcategory of the category given in the question.

```savedLean
example {α : InvolEndomap}
    : α.toEnd ⊚ α.toEnd ⊚ α.toEnd = α.toEnd := by
  rw [α.invol, Category.id_comp]
```

Or, more generally, that an involution will satisfy $`{\alpha^3 = \alpha}`.

```savedLean
example {𝒞 : Type u} [Category.{v, u} 𝒞] {A : 𝒞}
    (α : A ⟶ A) [IsInvolution α] : α ⊚ α ⊚ α = α := by
  rw [IsInvolution.invol, Category.id_comp]
```
:::

:::question (questionTitle := "Exercise 9") (questionPage := "141")
```savedComment
Exercise III.9 (p. 141)
```

```savedLean -show
namespace ExIII_9
```

In \[the category `Type`\], consider the endomap $`\alpha` of a three-element \[type $`A`\] defined by...

```savedLean
inductive A
  | a₁ | a₂ | a₃

def α : A ⟶ A
  | A.a₁ => A.a₂
  | A.a₂ => A.a₃
  | A.a₃ => A.a₂
```

Show that it satisfies $`{\alpha^3 = \alpha}`, but that it is _not_ idempotent and that it is _not_ an involution.
:::

:::solution (solutionTo := "Exercise 9")
We show that $`\alpha` satisfies $`{\alpha^3 = \alpha}`.

```savedLean
example : α ⊚ α ⊚ α = α := by
  funext x
  dsimp [CategoryStruct.comp, α]
  cases x <;> rfl
```

But $`\alpha` is not idempotent.

```savedLean
example : ¬(IsIdempotent α) := by
  by_contra h
  have h_contra : (α ⊚ α) A.a₁ = α A.a₁ := congrFun h.idem A.a₁
  dsimp [α] at h_contra
  contradiction
```

And $`\alpha` is not an involution.

```savedLean
example : ¬(IsInvolution α) := by
  by_contra h
  have h_contra : (α ⊚ α) A.a₁ = (𝟙 A) A.a₁ := congrFun h.invol A.a₁
  dsimp [α] at h_contra
  contradiction
```

```savedLean -show
end ExIII_9
```
:::

# 5. Irreflexive graphs

:::question (questionTitle := "Exercise 10") (questionPage := "141")
Complete the specification of the two maps
$$`X \xrightarrow{s} P \quad\text{and}\quad X \xrightarrow{t} P`
which express the source and target relations of the \[given graph\]. Is there any element of $`X` at which $`s` and $`t` take the same value in $`P`? Is there any element to which $`t` assigns the value $`k`?
:::

:::solution (solutionTo := "Exercise 10")
```savedComment
Exercise III.10 (p. 141)
```

```savedLean -show
namespace ExIII_10
```

The full specification of the two maps $`s` and $`t` is as follows:

```savedLean
inductive X
  | a | b | c | d | e

inductive P
  | k | m | n | p | q | r

def s : X ⟶ P
    | X.a => P.k
    | X.b => P.m
    | X.c => P.k
    | X.d => P.p
    | X.e => P.m

def t : X ⟶ P
    | X.a => P.m
    | X.b => P.m
    | X.c => P.m
    | X.d => P.q
    | X.e => P.r
```

$`s` and $`t` take the same value in $`P` at the element $`b` of $`X`.

```savedLean
example : s X.b = t X.b := rfl
```

There is no element to which $`t` assigns the value $`k`.

```savedLean
example : ¬(∃ x : X, t x = P.k) := by
  push_neg
  intro x
  cases x <;> simp [t]
```

```savedLean -show
end ExIII_10
```
:::

*The category 𝑺⇊ of (irreflexive directed multi-) graphs* is described on pp. 141–142. We implement the category 𝑺⇊ below.

```savedComment
The category 𝑺⇊ of (irreflexive directed multi-) graphs (pp. 141–142)
```

```savedLean
structure IrreflexiveGraph where
  tA : Type
  carrierA : Set tA
  tD : Type
  carrierD : Set tD
  toSrc : tA ⟶ tD
  toSrc_mem {a} : a ∈ carrierA → toSrc a ∈ carrierD
  toTgt : tA ⟶ tD
  toTgt_mem {a} : a ∈ carrierA → toTgt a ∈ carrierD

instance instCategoryIrreflexiveGraph : Category IrreflexiveGraph where
  Hom X Y := {
    f : (X.tA ⟶ Y.tA) × (X.tD ⟶ Y.tD) //
        (∀ x ∈ X.carrierA, f.1 x ∈ Y.carrierA) -- fA maps to codomain
        ∧ (∀ x ∈ X.carrierD, f.2 x ∈ Y.carrierD) -- fD maps to codomain
        ∧ f.2 ⊚ X.toSrc = Y.toSrc ⊚ f.1 -- source commutes
        ∧ f.2 ⊚ X.toTgt = Y.toTgt ⊚ f.1 -- target commutes
  }
  id X := ⟨
    (𝟙 X.tA, 𝟙 X.tD),
    by
      split_ands <;> first | exact fun _ hx ↦ hx | rfl
  ⟩
  comp := by
    rintro _ _ _ ⟨f, hf⟩ ⟨g, hg⟩
    exact ⟨
      (g.1 ⊚ f.1, g.2 ⊚ f.2),
      by
        obtain ⟨hfA_mtc, hfD_mtc, hfSrc_comm, hfTgt_comm⟩ := hf
        obtain ⟨hgA_mtc, hgD_mtc, hgSrc_comm, hgTgt_comm⟩ := hg
        split_ands
        · intro x hx
          exact hgA_mtc (f.1 x) (hfA_mtc x hx)
        · intro x hx
          exact hgD_mtc (f.2 x) (hfD_mtc x hx)
        · rw [← Category.assoc, hfSrc_comm, Category.assoc, hgSrc_comm,
              ← Category.assoc]
        · rw [← Category.assoc, hfTgt_comm, Category.assoc, hgTgt_comm,
              ← Category.assoc]
    ⟩
```

:::question (questionTitle := "Exercise 11") (questionPage := "142")
If $`f` is \[the map of graphs\]
$$`X \xrightarrow{f_A} Y,\; P \xrightarrow{f_D} Q`
and if
$$`Y \xrightarrow{g_A} Z,\; Q \xrightarrow{g_D} R`
is another map of graphs, show that the pair $`{g_A \circ f_A,\; g_D \circ f_D}` of 𝑺-composites is also an 𝑺⇊-map.
:::

:::solution (solutionTo := "Exercise 11")
```savedComment
Exercise III.11 (p. 142)
```

```savedLean -show
namespace ExIII_11
```

```savedLean
variable (X P Y Q Z R : Type)
         (s t : X ⟶ P) (s' t' : Y ⟶ Q) (s'' t'' : Z ⟶ R)

example (fA : X ⟶ Y) (fD : P ⟶ Q) (gA : Y ⟶ Z) (gD : Q ⟶ R)
    (hfSrc_comm : fD ⊚ s = s' ⊚ fA)
    (hfTgt_comm : fD ⊚ t = t' ⊚ fA)
    (hgSrc_comm : gD ⊚ s' = s'' ⊚ gA)
    (hgTgt_comm : gD ⊚ t' = t'' ⊚ gA)
    : (gD ⊚ fD) ⊚ s = s'' ⊚ (gA ⊚ fA)
        ∧ (gD ⊚ fD) ⊚ t = t'' ⊚ (gA ⊚ fA)
    := by
  constructor
  -- cf. instCategoryIrreflexiveGraph.comp above
  · rw [← Category.assoc, hfSrc_comm, Category.assoc, hgSrc_comm,
        ← Category.assoc]
  · rw [← Category.assoc, hfTgt_comm, Category.assoc, hgTgt_comm,
        ← Category.assoc]
```

Equivalently, we can use our implementation of the category 𝑺⇊ of graphs.

```savedLean
def graph (A D : Type) (src tgt : A ⟶ D) : IrreflexiveGraph := {
  tA := A
  carrierA := Set.univ
  tD := D
  carrierD := Set.univ
  toSrc := src
  toSrc_mem := fun _ ↦ Set.mem_univ _
  toTgt := tgt
  toTgt_mem := fun _ ↦ Set.mem_univ _
}

example (f : graph X P s t ⟶ graph Y Q s' t')
    (g : graph Y Q s' t' ⟶ graph Z R s'' t'')
    : graph X P s t ⟶ graph Z R s'' t'' := g ⊚ f
```

```savedLean -show
end ExIII_11
```
:::

# 6. Endomaps as special graphs

:::question (questionTitle := "Exercise 12") (questionPage := "143")
If we denote the result of the \[insertion\] process by $`I(f)`, then $`{I(g \circ f) = I(g) \circ I(f)}` so that our insertion $`I` preserves the fundamental operation of categories.
:::

:::solution (solutionTo := "Exercise 12")
```savedComment
Exercise III.12 (p. 143)
```

The insertion $`I` maps endomaps of sets to irreflexive graphs and maps morphisms between endomaps of sets to morphisms between irreflexive graphs — in other words, $`I` is a functor. We again use our implementation of the category 𝑺⇊ of graphs.

```savedLean
def functorSetWithEndomapToIrreflexiveGraph
    : Functor SetWithEndomap IrreflexiveGraph := {
  obj (X : SetWithEndomap) := {
    tA := X.t
    carrierA := Set.univ
    tD := X.t
    carrierD := Set.univ
    toSrc := 𝟙 X.t
    toSrc_mem := fun _ ↦ Set.mem_univ _
    toTgt := X.toEnd
    toTgt_mem := fun _ ↦ Set.mem_univ _
  }
  map {X Y : SetWithEndomap} (f : X ⟶ Y) := {
    val := (f, f)
    property := by
      obtain ⟨tX, carrierX, toEndX⟩ := X
      obtain ⟨tY, carrierY, toEndY⟩ := Y
      obtain ⟨f, hf_mtc, hf_comm⟩ := f
      dsimp at f hf_mtc hf_comm
      split_ands <;> (dsimp; intros; trivial)
  }
}

-- Helper function to align to the notation in the book
def I {X Y : SetWithEndomap} (f : X ⟶ Y) :=
  functorSetWithEndomapToIrreflexiveGraph.map f

example {X Y Z : SetWithEndomap}
    (f : X ⟶ Y) (g : Y ⟶ Z) : I (g ⊚ f) = I g ⊚ I f := rfl
```
:::

:::question (questionTitle := "Exercise 13") (questionPage := "144")
(Fullness) Show that if we are given any 𝑺⇊-morphism
$$`X \xrightarrow{f_A} Y,\; X \xrightarrow{f_D} Y`
between the special graphs that come via $`I` from endomaps of sets, then it follows that $`{f_A = f_D}`, so that the map itself comes via $`I` from a map in 𝑺↻.
:::

:::solution (solutionTo := "Exercise 13")
```savedComment
Exercise III.13 (p. 144)
```

```savedLean -show
namespace ExIII_13
```

```savedLean
variable (X' Y' : SetWithEndomap)
```

Using `Category IrreflexiveGraph`, we have

```savedLean
def graph₁ (S : SetWithEndomap) : IrreflexiveGraph := {
  tA := S.t
  carrierA := Set.univ
  tD := S.t
  carrierD := Set.univ
  toSrc := 𝟙 S.t
  toSrc_mem := fun _ ↦ Set.mem_univ _
  toTgt := S.toEnd
  toTgt_mem := fun _ ↦ Set.mem_univ _
}

variable (f₁ : graph₁ X' ⟶ graph₁ Y')

-- Align to the notation in the book: fA is f₁.val.1, fD is f₁.val.2
set_option quotPrecheck false
local notation "fA₁" => f₁.val.1
local notation "fD₁" => f₁.val.2
set_option quotPrecheck true

example : fA₁ = fD₁ := by
  obtain ⟨_, _ , hfSrc_comm, _⟩ := f₁.property
  dsimp [graph₁] at hfSrc_comm
  exact hfSrc_comm.symm
```

Alternatively, using `functorSetWithEndomapToIrreflexiveGraph`, we have

```savedLean
def graph₂ (S : SetWithEndomap) : IrreflexiveGraph :=
  functorSetWithEndomapToIrreflexiveGraph.obj S

variable (f₂ : graph₂ X' ⟶ graph₂ Y')

set_option quotPrecheck false
local notation "fA₂" => f₂.val.1
local notation "fD₂" => f₂.val.2
set_option quotPrecheck true

example : fA₂ = fD₂ := by
  obtain ⟨_, _ , hfSrc_comm, _⟩ := f₂.property
  dsimp [graph₂, functorSetWithEndomapToIrreflexiveGraph]
      at hfSrc_comm
  exact hfSrc_comm.symm
```

```savedLean -show
end ExIII_13
```
:::

# 7. The simpler category 𝑺↓: Objects are just maps of sets

*The category 𝑺↓ of simple directed graphs* is described on pp. 144–145. We implement the category 𝑺↓ below.

```savedComment
The category 𝑺↓ of simple directed graphs (pp. 144–145)
```

```savedLean
structure SimpleGraph where
  tA : Type
  carrierA : Set tA
  tD : Type
  carrierD : Set tD
  toFun : tA ⟶ tD
  toFun_mem {a} : a ∈ carrierA → toFun a ∈ carrierD

instance : Category SimpleGraph where
  Hom X Y := {
    f : (X.tA ⟶ Y.tA) × (X.tD ⟶ Y.tD) //
        (∀ x ∈ X.carrierA, f.1 x ∈ Y.carrierA) -- fA maps to codomain
        ∧ (∀ x ∈ X.carrierD, f.2 x ∈ Y.carrierD) -- fD maps to codomain
        ∧ f.2 ⊚ X.toFun = Y.toFun ⊚ f.1 -- commutes
  }
  id X := ⟨
    (𝟙 X.tA, 𝟙 X.tD),
    by
      split_ands <;> first | exact fun _ hx ↦ hx | rfl
  ⟩
  comp := by
    rintro _ _ _ ⟨f, hf⟩ ⟨g, hg⟩
    exact ⟨
      (g.1 ⊚ f.1, g.2 ⊚ f.2),
      by
        obtain ⟨hfA_mtc, hfD_mtc, hfSrc_comm⟩ := hf
        obtain ⟨hgA_mtc, hgD_mtc, hgSrc_comm⟩ := hg
        split_ands
        · intro x hx
          exact hgA_mtc (f.1 x) (hfA_mtc x hx)
        · intro x hx
          exact hgD_mtc (f.2 x) (hfD_mtc x hx)
        · rw [← Category.assoc, hfSrc_comm, Category.assoc, hgSrc_comm,
              ← Category.assoc]
    ⟩
```

The insertion $`J` is a functor from 𝑺↻ to 𝑺↓.

```savedLean
def functorSetWithEndomapToSimpleGraph
    : Functor SetWithEndomap SimpleGraph := {
  obj (X : SetWithEndomap) := {
    tA := X.t
    carrierA := Set.univ
    tD := X.t
    carrierD := Set.univ
    toFun := X.toEnd
    toFun_mem := fun _ ↦ Set.mem_univ _
  }
  map {X Y : SetWithEndomap} (f : X ⟶ Y) := {
    val := (f, f)
    property := by
      obtain ⟨tX, carrierX, toEndX⟩ := X
      obtain ⟨tY, carrierY, toEndY⟩ := Y
      obtain ⟨f, hf_mtc, hf_comm⟩ := f
      dsimp at f hf_mtc hf_comm
      split_ands <;> (dsimp; intros; trivial)
  }
}

-- Helper function to align to the notation in the book
def J {X Y : SetWithEndomap} (f : X ⟶ Y) :=
  functorSetWithEndomapToSimpleGraph.map f

example {X Y Z : SetWithEndomap}
    (f : X ⟶ Y) (g : Y ⟶ Z) : J (g ⊚ f) = J g ⊚ J f := rfl
```

:::question (questionTitle := "Exercise 14") (questionPage := "144")
Give an example of 𝑺 of two endomaps and two maps as in
$$`X \xrightarrow{f_A} Y,\; X \xrightarrow{f_D} Y,\; X \xrightarrow{\alpha} X,\; Y \xrightarrow{\beta} Y`
which satisfy the equation $`{f_D \circ \alpha = \beta \circ f_A}`, but for which $`{f_A \ne f_D}`.
:::

:::solution (solutionTo := "Exercise 14")
```savedComment
Exercise III.14 (p. 144)
```

```savedLean -show
namespace ExIII_14
```

We give $`X`, $`Y`, $`\alpha`, $`\beta`, $`f_A`, $`f_D` as follows:

```savedLean
inductive X
  | x₁ | x₂

inductive Y
  | y₁ | y₂

def α : X ⟶ X
  | X.x₁ => X.x₁
  | X.x₂ => X.x₁

def β : Y ⟶ Y
  | Y.y₁ => Y.y₁
  | Y.y₂ => Y.y₁

def fA : X ⟶ Y
  | X.x₁ => Y.y₁
  | X.x₂ => Y.y₂

def fD : X ⟶ Y
  | X.x₁ => Y.y₁
  | X.x₂ => Y.y₁
```

We show that our example satisfies the required properties.

```savedLean
example : fD ⊚ α = β ⊚ fA ∧ fA ≠ fD := by
  constructor
  · funext x
    cases x <;> rfl
  · by_contra h
    have h_contra : fA X.x₂ = fD X.x₂ := congrFun h X.x₂
    dsimp [fA, fD] at h_contra
    contradiction
```

```savedLean -show
end ExIII_14
```
:::

# 8. Reflexive graphs

*The category of reflexive graphs* is described on p. 145. We implement this category below.

```savedComment
The category of reflexive graphs (p. 145)
```

```savedLean
structure ReflexiveGraph extends IrreflexiveGraph where
  toCommonSection : tD ⟶ tA
  toCommonSection_mem {d} : d ∈ carrierD → toCommonSection d ∈ carrierA
  section_src : toSrc ⊚ toCommonSection = 𝟙 tD
  section_tgt : toTgt ⊚ toCommonSection = 𝟙 tD

instance : Category ReflexiveGraph where
  Hom X Y := {
    f : (X.tA ⟶ Y.tA) × (X.tD ⟶ Y.tD) //
        (∀ x ∈ X.carrierA, f.1 x ∈ Y.carrierA) -- fA maps to codomain
        ∧ (∀ x ∈ X.carrierD, f.2 x ∈ Y.carrierD) -- fD maps to codomain
        ∧ f.2 ⊚ X.toSrc = Y.toSrc ⊚ f.1 -- source commutes
        ∧ f.2 ⊚ X.toTgt = Y.toTgt ⊚ f.1 -- target commutes
        ∧ f.1 ⊚ X.toCommonSection = Y.toCommonSection ⊚ f.2
  }
  id X := ⟨
    (𝟙 X.tA, 𝟙 X.tD),
    by
      split_ands <;> first | exact fun _ hx ↦ hx | rfl
  ⟩
  comp := by
    rintro _ _ _ ⟨f, hf⟩ ⟨g, hg⟩
    exact ⟨
      (g.1 ⊚ f.1, g.2 ⊚ f.2),
      by
        obtain ⟨hfA_mtc, hfD_mtc, hfSrc_comm, hfTgt_comm,
            hfCommonSection_comm⟩ := hf
        obtain ⟨hgA_mtc, hgD_mtc, hgSrc_comm, hgTgt_comm,
            hgCommonSection_comm⟩ := hg
        split_ands
        · intro x hx
          exact hgA_mtc (f.1 x) (hfA_mtc x hx)
        · intro x hx
          exact hgD_mtc (f.2 x) (hfD_mtc x hx)
        · rw [← Category.assoc, hfSrc_comm, Category.assoc, hgSrc_comm,
              ← Category.assoc]
        · rw [← Category.assoc, hfTgt_comm, Category.assoc, hgTgt_comm,
              ← Category.assoc]
        · rw [← Category.assoc, hfCommonSection_comm, Category.assoc,
              hgCommonSection_comm, ← Category.assoc]
    ⟩
```

:::question (questionTitle := "Exercise 15") (questionPage := "145")
In a reflexive graph, the two endomaps $`{e_1 = is}`, $`{e_0 = it}` of the set of arrows are not only idempotent, but even satisfy _four_ equations:
$$`e_k e_j = e_j \quad\text{for}\quad k, j = 0, 1.`
:::

:::solution (solutionTo := "Exercise 15")
```savedComment
Exercise III.15 (p. 145)
```

```savedLean -show
namespace ExIII_15
```

We use our implementation of the category of reflexive graphs.

```savedLean
variable (X : ReflexiveGraph)
```

Define the two endomaps $`{e_1 = is}`, $`{e_0 = it}`.

```savedLean
variable (e₁ e₀ : X.tA ⟶ X.tA)
         (h₁ : e₁ = X.toCommonSection ⊚ X.toSrc)
         (h₀ : e₀ = X.toCommonSection ⊚ X.toTgt)
```

$`e_0 e_0 = e_0`

```savedLean
example : e₀ ⊚ e₀ = e₀ := by
  rw [h₀, Category.assoc, ← Category.assoc X.toCommonSection,
      X.section_tgt, Category.id_comp]
```

$`e_0 e_1 = e_1`

```savedLean
example : e₀ ⊚ e₁ = e₁ := by
  rw [h₀, h₁, Category.assoc, ← Category.assoc X.toCommonSection,
      X.section_tgt, Category.id_comp]
```

$`e_1 e_0 = e_0`

```savedLean
example : e₁ ⊚ e₀ = e₀ := by
  rw [h₁, h₀, Category.assoc, ← Category.assoc X.toCommonSection,
      X.section_src, Category.id_comp]
```

$`e_1 e_1 = e_1`

```savedLean
example : e₁ ⊚ e₁ = e₁ := by
  rw [h₁, Category.assoc, ← Category.assoc X.toCommonSection,
      X.section_src, Category.id_comp]
```

```savedLean -show
end ExIII_15
```
:::

:::question (questionTitle := "Exercise 16") (questionPage := "145")
Show that if $`f_A`, $`f_D` in 𝑺 constitute a map of reflexive graphs, then $`f_D` is determined by $`f_A` and the internal structure of the two graphs.
:::

:::solution (solutionTo := "Exercise 16")
```savedComment
Exercise III.16 (p. 145)
```

```savedLean -show
namespace ExIII_16
```

$`f` is a morphism in our category of reflexive graphs.

```savedLean
variable (X Y : ReflexiveGraph) (f : X ⟶ Y)

-- Align to the notation in the book
set_option quotPrecheck false
local notation "fA" => f.val.1
local notation "fD" => f.val.2
set_option quotPrecheck true

local notation "s" => X.toSrc
local notation "s'" => Y.toSrc
local notation "t" => X.toTgt
local notation "t'" => Y.toTgt
local notation "i" => X.toCommonSection
local notation "i'" => Y.toCommonSection
```

Then $`f_D` is determined by $`f_A` and the internal structure of the two graphs.

```savedLean
example : fD = s' ⊚ fA ⊚ i := by
  rw [← Category.id_comp fD, ← X.section_src]
  repeat rw [Category.assoc]
  congrm ?_ ⊚ X.toCommonSection
  exact f.property.2.2.1
```

Or, alternatively,

```savedLean
example : fD = t' ⊚ fA ⊚ i := by
  rw [← Category.id_comp fD, ← X.section_tgt]
  repeat rw [Category.assoc]
  congrm ?_ ⊚ X.toCommonSection
  exact f.property.2.2.2.1
```

```savedLean -show
end ExIII_16
```
:::

:::question (questionTitle := "Exercise 17") (questionPage := "145")
Consider a structure involving two sets and four maps as in
$$`M \xrightarrow{\varphi} M,\; F \xrightarrow{\varphi'} M,\; F \xrightarrow{\mu} F,\; M \xrightarrow{\mu'} F \quad\text{(no equations required)}`
(for example $`{M = \mathit{males}}`, $`{F = \mathit{females}}`, $`\varphi` and $`\varphi'` are $`\mathit{father}`, and $`\mu` and $`\mu'` are $`\mathit{mother}`). Devise a rational definition of _map_ between such structures in order to make them into a category.
:::

:::solution (solutionTo := "Exercise 17")
```savedComment
Exercise III.17 (p. 145)
```

```savedLean -show
namespace ExIII_17
```

Define the structure.

```savedLean
structure ParentLike where
  tM : Type
  carrierM : Set tM
  tF : Type
  carrierF : Set tF
  φ : tM ⟶ tM
  φ_mem {m} : m ∈ carrierM → φ m ∈ carrierM
  φ' : tF ⟶ tM
  φ'_mem {f} : f ∈ carrierF → φ' f ∈ carrierM
  μ : tF ⟶ tF
  μ_mem {f} : f ∈ carrierF → μ f ∈ carrierF
  μ' : tM ⟶ tF
  μ'_mem {m} : m ∈ carrierM → μ' m ∈ carrierF
```

Define a map between such structures.

```savedLean
def ParentLikeHom (X Y : ParentLike) := {
  f : (X.tM ⟶ Y.tM) × (X.tF ⟶ Y.tF) //
      (∀ x ∈ X.carrierM, f.1 x ∈ Y.carrierM) -- f.1 maps to codomain
      ∧ (∀ x ∈ X.carrierF, f.2 x ∈ Y.carrierF) -- f.2 maps to codomain
      ∧ f.1 ⊚ X.φ = Y.φ ⊚ f.1 -- φ commutes
      ∧ f.1 ⊚ X.φ' = Y.φ' ⊚ f.2 -- φ' commutes
      ∧ f.2 ⊚ X.μ = Y.μ ⊚ f.2 -- μ commutes
      ∧ f.2 ⊚ X.μ' = Y.μ' ⊚ f.1 -- μ' commutes
}
```

This map between structures makes them into a category.

```savedLean
instance : Category ParentLike where
  Hom := ParentLikeHom -- our map between ParentLike structures
  id X := ⟨
    (𝟙 X.tM, 𝟙 X.tF),
    by
      split_ands <;> first | exact fun _ hx ↦ hx | rfl
  ⟩
  comp := by
    rintro _ _ _ ⟨f, hf⟩ ⟨g, hg⟩
    exact ⟨
      (g.1 ⊚ f.1, g.2 ⊚ f.2),
      by
        obtain ⟨hfM_mtc, hfF_mtc, hfφ_comm, hfφ'_comm, hfμ_comm,
            hfμ'_comm⟩ := hf
        obtain ⟨hgM_mtc, hgF_mtc, hgφ_comm, hgφ'_comm, hgμ_comm,
            hgμ'_comm⟩ := hg
        split_ands
        · intro x hx
          exact hgM_mtc (f.1 x) (hfM_mtc x hx)
        · intro x hx
          exact hgF_mtc (f.2 x) (hfF_mtc x hx)
        · rw [← Category.assoc, hfφ_comm, Category.assoc, hgφ_comm,
              ← Category.assoc]
        · rw [← Category.assoc, hfφ'_comm, Category.assoc, hgφ'_comm,
              ← Category.assoc]
        · rw [← Category.assoc, hfμ_comm, Category.assoc, hgμ_comm,
              ← Category.assoc]
        · rw [← Category.assoc, hfμ'_comm, Category.assoc, hgμ'_comm,
              ← Category.assoc]
    ⟩
```

```savedLean -show
end ExIII_17
```
:::

# 10. Retractions and injectivity

:::definition (definitionTerm := "Injective") (definitionPage := "146")
We say that a map $`{X \xrightarrow{a} Y}` is _injective_ iff for any maps $`{T \xrightarrow{x_1} X}` and $`{T \xrightarrow{x_2} X}` (in the same category) if $`{ax_1 = ax_2}` then $`{x_1 = x_2}` (or, in contrapositive form, 'the map $`a` does not destroy distinctions', i.e. if $`{x_1 \ne x_2}`..., then $`{ax_1 \ne ax_2}` as well).
:::

cf. the earlier definition of _injective_ on p. 52.

:::question (questionTitle := "Exercise 18") (questionPage := "146")
If $`a` has a retraction, then $`a` is injective. (Assume $`{pa = 1_X}` and $`{ax_1 = ax_2}`; then try to show by calculation that $`{x_1 = x_2}`.)
:::

:::solution (solutionTo := "Exercise 18")
```savedComment
Exercise III.18 (p. 146)
```

cf. `mono_iff_injective`.

```savedLean
example {𝒞 : Type u} [Category.{v, u} 𝒞] {X Y T : 𝒞}
    {a : X ⟶ Y} {p : Y ⟶ X} {x₁ x₂ : T ⟶ X}
    (h₁ : p ⊚ a = 𝟙 X) (h₂ : a ⊚ x₁ = a ⊚ x₂)
    : x₁ = x₂ := by
  calc x₁
    _ = 𝟙 X ⊚ x₁ := by rw [Category.comp_id]
    _ = (p ⊚ a) ⊚ x₁ := by rw [h₁]
    _ = p ⊚ a ⊚ x₁ := by rw [Category.assoc]
    _ = p ⊚ a ⊚ x₂ := by rw [h₂]
    _ = (p ⊚ a) ⊚ x₂ := by rw [Category.assoc]
    _ = 𝟙 X ⊚ x₂ := by rw [h₁]
    _ = x₂ := by rw [Category.comp_id]
```
:::

Exercises 19–24 that follow relate to the sets $`X` and $`Y`, the endomaps $`\alpha` and $`\beta`, and the map $`a` as defined below. (Note that we in fact define $`X` and $`Y` as finite types rather than finite sets.)

```savedLean -show
namespace ExIII_19_24
```

```savedLean
inductive X
  | x₀ | x₁
  deriving Fintype

inductive Y
  | y₀ | y₁ | y₂
  deriving Fintype

def α : X ⟶ X
  | X.x₀ => X.x₀
  | X.x₁ => X.x₀

def β : Y ⟶ Y
  | Y.y₀ => Y.y₀
  | Y.y₁ => Y.y₀
  | Y.y₂ => Y.y₁

def a : X ⟶ Y
  | X.x₀ => Y.y₀
  | X.x₁ => Y.y₁
```

:::question (questionTitle := "Exercise 19") (questionPage := "147")
Show that $`a` is a map $`{X^{↻\alpha} \xrightarrow{a} Y^{↻\beta}}` in 𝑺↻.
:::

:::solution (solutionTo := "Exercise 19")
```savedComment
Exercise III.19 (p. 147)
```

$`a` is a map in 𝑺↻ if it satisfies the condition $`{a \alpha = \beta a}`.

```savedLean
example : a ⊚ α = β ⊚ a := by
  funext x
  cases x <;> rfl
```

Or, alternatively, using the categorical framework we defined earlier, $`a` is a map in 𝑺↻ if it is a morphism in our category of endomaps of sets.

```savedLean
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

def a' : Xα ⟶ Yβ := ⟨
  a,
  by
    constructor
    · exact fun _ _ ↦ Set.mem_univ _
    · funext x
      cases x <;> rfl
⟩
```
:::

:::question (questionTitle := "Exercise 20") (questionPage := "147")
Show that $`a` is _injective_.
:::

:::solution (solutionTo := "Exercise 20")
```savedComment
Exercise III.20 (p. 147)
```

cf. Exercise 18 above.

```savedLean
example : ∀ {T : Type} (x₁ x₂ : T ⟶ X),
    a ⊚ x₁ = a ⊚ x₂ → x₁ = x₂ := by
  let p : Y ⟶ X
    | Y.y₀ => X.x₀
    | Y.y₁ => X.x₁
    | Y.y₂ => X.x₁
  have h₁ : p ⊚ a = 𝟙 X := by
    funext x
    cases x <;> rfl
  intro _ x₁ x₂ h₂
  calc x₁
    _ = 𝟙 X ⊚ x₁ := by rw [Category.comp_id]
    _ = (p ⊚ a) ⊚ x₁ := by rw [h₁]
    _ = p ⊚ a ⊚ x₁ := by rw [Category.assoc]
    _ = p ⊚ a ⊚ x₂ := by rw [h₂]
    _ = (p ⊚ a) ⊚ x₂ := by rw [Category.assoc]
    _ = 𝟙 X ⊚ x₂ := by rw [h₁]
    _ = x₂ := by rw [Category.comp_id]
```
:::

:::question (questionTitle := "Exercise 21") (questionPage := "147")
Show that, as a map $`{X \xrightarrow{a} Y}` in 𝑺, $`a` has exactly two retractions $`p`.
:::

:::solution (solutionTo := "Exercise 21")
```savedComment
Exercise III.21 (p. 147)
```

We found one retraction $`p_1` in Exercise 20.

```savedLean
def p₁ : Y ⟶ X
  | Y.y₀ => X.x₀
  | Y.y₁ => X.x₁
  | Y.y₂ => X.x₁

example : p₁ ⊚ a = 𝟙 X := by
  funext x
  cases x <;> rfl
```

Using $`p_1` with Danilo's formula, we find that $`a` has exactly two retractions.

```savedLean (name := outIII_21)
#eval Danilo's_formula (Finset.univ) (Finset.univ) a p₁
  (by funext x; fin_cases x <;> rfl)
  (by intro x y _; fin_cases x <;> fin_cases y <;>
    (first | rfl | simp; trivial))
```

```leanOutput outIII_21
2
```

The other retraction $`p_2` is

```savedLean
def p₂ : Y ⟶ X
  | Y.y₀ => X.x₀
  | Y.y₁ => X.x₁
  | Y.y₂ => X.x₀

example : p₂ ⊚ a = 𝟙 X := by
  funext x
  cases x <;> rfl
```
:::

:::question (questionTitle := "Exercise 22") (questionPage := "147")
Show that neither of the maps $`p` found in the preceding exercise is _a map_ $`{Y^{↻\beta} \rightarrow X^{↻\alpha}}` in 𝑺↻. Hence $`a` has no retractions in 𝑺↻.
:::

:::solution (solutionTo := "Exercise 22")
```savedComment
Exercise III.22 (p. 147)
```

$`p_1` is not a map $`{Y^{↻\beta} \rightarrow X^{↻\alpha}}` in 𝑺↻.

```savedLean
example : ¬(p₁ ⊚ β = α ⊚ p₁) := by
  intro h
  have h_contra : (p₁ ⊚ β) Y.y₂ = (α ⊚ p₁) Y.y₂ := congrFun h Y.y₂
  dsimp [p₁, α, β] at h_contra
  contradiction
```

$`p_2` is not a map $`{Y^{↻\beta} \rightarrow X^{↻\alpha}}` in 𝑺↻.

```savedLean
example : ¬(p₂ ⊚ β = α ⊚ p₂) := by
  intro h
  have h_contra : (p₂ ⊚ β) Y.y₂ = (α ⊚ p₂) Y.y₂ := congrFun h Y.y₂
  dsimp [p₂, α, β] at h_contra
  contradiction
```

Since, by Exercise 21, $`p_1` and $`p_2` are the only retractions of $`a` in 𝑺, they are the only candidates for retractions of $`a` in 𝑺↻; hence $`a` has no retractions in 𝑺↻.
:::

:::question (questionTitle := "Exercise 23") (questionPage := "147")
How many of the eight 𝑺-maps $`{Y \rightarrow X}` (if any) are actually 𝑺↻-maps?
$$`Y^{↻\beta} \rightarrow X^{↻\alpha}`
:::

:::solution (solutionTo := "Exercise 23")
```savedComment
Exercise III.23 (p. 147)
```

For an 𝑺-map $`b` to be an 𝑺↻-map, we require that $`{b \beta = \alpha b}`. Since $`{\alpha b = x_0}`, it follows that we require $`{b \beta = x_0}`. That is, we require $`{b(y_0) = x_0}` and $`{b(y_1) = x_0}`, which leaves $`b(y_2)` as the only degree of freedom. Hence just two of the eight 𝑺-maps $`{Y \rightarrow X}` are actually 𝑺↻-maps $`{Y^{↻\beta} \rightarrow X^{↻\alpha}}`, as given below.

The 𝑺-maps $`b_1` and $`b_2` are 𝑺↻-maps.

```savedLean
def b₁ : Y ⟶ X
  | Y.y₀ => X.x₀
  | Y.y₁ => X.x₀
  | Y.y₂ => X.x₀

example : b₁ ⊚ β = α ⊚ b₁ := by
  funext y
  cases y <;> rfl

def b₂ : Y ⟶ X
  | Y.y₀ => X.x₀
  | Y.y₁ => X.x₀
  | Y.y₂ => X.x₁

example : b₂ ⊚ β = α ⊚ b₂ := by
  funext y
  cases y <;> rfl
```

The remaining 𝑺-maps $`b_3` to $`b_8` are not 𝑺↻-maps.

```savedLean
def b₃ : Y ⟶ X
  | Y.y₀ => X.x₁
  | Y.y₁ => X.x₀
  | Y.y₂ => X.x₀

example : b₃ ⊚ β ≠ α ⊚ b₃ := by
  by_contra h
  have h_contra : (b₃ ⊚ β) Y.y₀ = (α ⊚ b₃) Y.y₀ := congrFun h Y.y₀
  dsimp [b₃, α, β] at h_contra
  contradiction

def b₄ : Y ⟶ X
  | Y.y₀ => X.x₁
  | Y.y₁ => X.x₀
  | Y.y₂ => X.x₁

example : b₄ ⊚ β ≠ α ⊚ b₄ := by
  by_contra h
  have h_contra : (b₄ ⊚ β) Y.y₀ = (α ⊚ b₄) Y.y₀ := congrFun h Y.y₀
  dsimp [b₄, α, β] at h_contra
  contradiction

def b₅ : Y ⟶ X
  | Y.y₀ => X.x₀
  | Y.y₁ => X.x₁
  | Y.y₂ => X.x₀

example : b₅ ⊚ β ≠ α ⊚ b₅ := by
  by_contra h
  have h_contra : (b₅ ⊚ β) Y.y₂ = (α ⊚ b₅) Y.y₂ := congrFun h Y.y₂
  dsimp [b₅, α, β] at h_contra
  contradiction

def b₆ : Y ⟶ X
  | Y.y₀ => X.x₀
  | Y.y₁ => X.x₁
  | Y.y₂ => X.x₁

example : b₆ ⊚ β ≠ α ⊚ b₆ := by
  by_contra h
  have h_contra : (b₆ ⊚ β) Y.y₂ = (α ⊚ b₆) Y.y₂ := congrFun h Y.y₂
  dsimp [b₆, α, β] at h_contra
  contradiction

def b₇ : Y ⟶ X
  | Y.y₀ => X.x₁
  | Y.y₁ => X.x₁
  | Y.y₂ => X.x₀

example : b₇ ⊚ β ≠ α ⊚ b₇ := by
  by_contra h
  have h_contra : (b₇ ⊚ β) Y.y₂ = (α ⊚ b₇) Y.y₂ := congrFun h Y.y₂
  dsimp [b₇, α, β] at h_contra
  contradiction

def b₈ : Y ⟶ X
  | Y.y₀ => X.x₁
  | Y.y₁ => X.x₁
  | Y.y₂ => X.x₁

example : b₈ ⊚ β ≠ α ⊚ b₈ := by
  by_contra h
  have h_contra : (b₈ ⊚ β) Y.y₂ = (α ⊚ b₈) Y.y₂ := congrFun h Y.y₂
  dsimp [b₈, α, β] at h_contra
  contradiction
```
:::

:::question (questionTitle := "Exercise 24") (questionPage := "147")
Show that our map $`a` does not have any retractions, even when considered (via the insertion $`J` in Section 7 of this article) as being a map in the 'looser' category 𝑺↓.
:::

:::solution (solutionTo := "Exercise 24")
```savedComment
Exercise III.24 (p. 147)
```

Emulating the insertion $`J`,

```savedLean
def X' : SimpleGraph := {
  tA := X
  carrierA := Set.univ
  tD := X
  carrierD := Set.univ
  toFun := α
  toFun_mem := fun _ ↦ Set.mem_univ _
}

def Y' : SimpleGraph := {
  tA := Y
  carrierA := Set.univ
  tD := Y
  carrierD := Set.univ
  toFun := β
  toFun_mem := fun _ ↦ Set.mem_univ _
}

def a'' : X' ⟶ Y' := ⟨
  (a, a),
  by
    split_ands
    · exact fun _ _ ↦ Set.mem_univ _
    · exact fun _ _ ↦ Set.mem_univ _
    · funext x
      cases x <;> rfl
⟩
```

we can show that $`a` has no retractions.

```savedLean
example : ¬(∃ p : Y' ⟶ X', p ⊚ a'' = 𝟙 X') := by
  push_neg
  intro p
  obtain ⟨p, _, _, hp_comm⟩ := p
  dsimp [X', Y'] at hp_comm
  have hpβ₀ : ∀ y, (α ⊚ p.1) y = X.x₀ := by
    intro y
    dsimp [α]
    cases p.1 y <;> rfl
  rw [← hp_comm] at hpβ₀
  dsimp [Y'] at hpβ₀
  have hpβ : p.2 (β Y.y₂) = X.x₀ := hpβ₀ Y.y₂
  have hβ : β Y.y₂ = Y.y₁ := rfl
  rw [hβ] at hpβ
  dsimp [CategoryStruct.comp, CategoryStruct.id, a'']
  by_contra h₁
  have h₂ : (p.1 ⊚ a, p.2 ⊚ a) = (𝟙 X, 𝟙 X) :=
    congrArg Subtype.val h₁
  have h₃ : p.2 ⊚ a = 𝟙 X := congrArg Prod.snd h₂
  have hpa₀ : ∀ x, p.2 (a x) = x := congrFun h₃
  have hpa : p.2 (a X.x₁) = X.x₁ := hpa₀ X.x₁
  have ha : a X.x₁ = Y.y₁ := rfl
  rw [ha] at hpa
  rw [hpβ] at hpa
  contradiction
```

Or, alternatively, using our functor `J` defined earlier,

```savedLean
example : ¬(∃ p : Yβ ⟶ Xα, J p ⊚ J a' = J (𝟙 Xα)) := by
  push_neg
  intro p
  obtain ⟨p, _, hp_comm⟩ := p
  dsimp [Xα, Yβ] at hp_comm
  have hpβ₀ : ∀ y, (α ⊚ p) y = X.x₀ := by
    intro y
    dsimp [α]
    cases p y <;> rfl
  rw [← hp_comm] at hpβ₀
  dsimp [Yβ] at hpβ₀
  have hpβ : p (β Y.y₂) = X.x₀ := hpβ₀ Y.y₂
  have hβ : β Y.y₂ = Y.y₁ := rfl
  rw [hβ] at hpβ
  dsimp [CategoryStruct.comp, CategoryStruct.id, a', J,
      functorSetWithEndomapToSimpleGraph]
  by_contra h₁
  have h₂ : (p ⊚ a, p ⊚ a) = (𝟙 X, 𝟙 X) :=
    congrArg Subtype.val h₁
  have h₃ : p ⊚ a = 𝟙 X := congrArg Prod.snd h₂
  have hpa₀ : ∀ x, p (a x) = x := congrFun h₃
  have hpa : p (a X.x₁) = X.x₁ := hpa₀ X.x₁
  have ha : a X.x₁ = Y.y₁ := rfl
  rw [ha] at hpa
  rw [hpβ] at hpa
  contradiction
```
:::

```savedLean -show
end ExIII_19_24
```

:::question (questionTitle := "Exercise 25") (questionPage := "148")
Show that for any two graphs and any 𝑺⇊-map between them
$$`X \xrightarrow{f_A} Y,\; P \xrightarrow{f_D} Q,\; X \xrightarrow{s} P,\; X \xrightarrow{t} P,\; Y \xrightarrow{s'} Q,\; Y \xrightarrow{t'} Q`
the equation $`{f_D \circ s = f_D \circ t}` can only be true when $`f_A` maps every arrow in $`X` to a _loop_ (relative to $`s'`, $`t'`) in $`Y`.
:::

:::solution (solutionTo := "Exercise 25")
```savedComment
Exercise III.25 (p. 148)
```

```savedLean -show
namespace ExIII_25
```

We first give a proof without using `Category IrreflexiveGraph` that we defined previously.

```savedLean
example {X P Y Q : Type}
    (s t : X ⟶ P) (s' t' : Y ⟶ Q) (fA : X ⟶ Y) (fD : P ⟶ Q)
    (hfSrc_comm : fD ⊚ s = s' ⊚ fA) (hfTgt_comm : fD ⊚ t = t' ⊚ fA)
    : fD ⊚ s = fD ⊚ t ↔ ∀ x, s' (fA x) = t' (fA x) := by
  constructor
  · intro h x
    change (s' ⊚ fA) x = (t' ⊚ fA) x
    rw [← hfSrc_comm, ← hfTgt_comm]
    exact congrFun h x
  · intro h
    rw [hfSrc_comm, hfTgt_comm]
    funext x
    exact h x
```

Using `Category IrreflexiveGraph`, we have

```savedLean
variable (XP YQ : IrreflexiveGraph) (f : XP ⟶ YQ)

-- Align to the notation in the book
set_option quotPrecheck false
local notation "fA" => f.val.1
local notation "fD" => f.val.2
set_option quotPrecheck true

local notation "s" => XP.toSrc
local notation "s'" => YQ.toSrc
local notation "t" => XP.toTgt
local notation "t'" => YQ.toTgt

example : (fD ⊚ s = fD ⊚ t) ↔ (∀ x, s' (fA x) = t' (fA x)) := by
  obtain ⟨f, _, _, hfSrc_comm, hfTgt_comm⟩ := f
  dsimp
  constructor
  · intro h x
    change (s' ⊚ f.1) x = (t' ⊚ f.1) x
    rw [← hfSrc_comm, ← hfTgt_comm]
    exact congrFun h x
  · intro h
    rw [hfSrc_comm, hfTgt_comm]
    funext x
    exact h x
```

```savedLean -show
end ExIII_25
```
:::

:::question (questionTitle := "Exercise 26") (questionPage := "148")
There is an 'inclusion' map $`{\mathbb{Z} \xrightarrow{f} \mathbb{Q}}` in 𝑺 for which

1. $`{\mathbb{Z}^{↻5\times()} \xrightarrow{f} \mathbb{Q}^{↻5\times()}}` is a map in 𝑺↻, and
2. $`\mathbb{Q}^{↻5\times()}` is an automorphism, and
3. $`f` is _injective_.

Find the $`f` and prove the three statements.
:::

:::solution (solutionTo := "Exercise 26")
```savedComment
Exercise III.26 (p. 148)
```

```savedLean -show
namespace ExIII_26
```

Rule is $`{f(x) = x / 1}`.

```savedLean
def f : ℤ ⟶ ℚ := fun x ↦ (x : ℚ)
```

1\. We show that $`{\mathbb{Z}^{↻5\times()} \xrightarrow{f} \mathbb{Q}^{↻5\times()}}` is a map in 𝑺↻.

```savedLean
def Z : SetWithEndomap := {
  t := ℤ
  carrier := Set.univ
  toEnd := fun x ↦ 5 * x
  toEnd_mem := fun _ ↦ Set.mem_univ _
}

def Q : SetWithEndomap := {
  t := ℚ
  carrier := Set.univ
  toEnd := fun x ↦ 5 * x
  toEnd_mem := fun _ ↦ Set.mem_univ _
}

example : Z ⟶ Q := ⟨
  f,
  by
    constructor
    · exact fun _ _ ↦ Set.mem_univ _
    · funext (x : ℤ)
      dsimp [Z, Q, f]
      norm_cast
⟩
```

2\. We show that $`\mathbb{Q}^{↻5\times()}` is an automorphism.

```savedLean
example : SetWithInvEndomap := {
  t := Q.t
  carrier := Q.carrier
  toEnd := Q.toEnd
  toEnd_mem := fun _ ↦ Set.mem_univ _
  inv := by
    let finv : ℚ ⟶ ℚ := fun x ↦ x / 5
    use finv
    constructor <;> (funext x; dsimp [finv, Q]; ring)
}
```

3\. We show that $`f` is _injective_.

```savedLean
example : ∀ {T : Type} (x₁ x₂ : T ⟶ ℤ),
    f ⊚ x₁ = f ⊚ x₂ → x₁ = x₂ := by
  let p : ℚ ⟶ ℤ := fun y ↦ y.num
  have h₁ : p ⊚ f = 𝟙 ℤ := by
    dsimp [f, p]
    funext x
    congr
  intro _ x₁ x₂ h₂
  calc x₁
    _ = 𝟙 ℤ ⊚ x₁ := by rw [Category.comp_id]
    _ = (p ⊚ f) ⊚ x₁ := by rw [h₁]
    _ = p ⊚ f ⊚ x₁ := by rw [Category.assoc]
    _ = p ⊚ f ⊚ x₂ := by rw [h₂]
    _ = (p ⊚ f) ⊚ x₂ := by rw [Category.assoc]
    _ = 𝟙 ℤ ⊚ x₂ := by rw [h₁]
    _ = x₂ := by rw [Category.comp_id]
```

```savedLean -show
end ExIII_26
```
:::

:::question (questionTitle := "Exercise 27") (questionPage := "148")
```savedComment
Exercise III.27 (p. 148)
```

```savedLean -show
namespace ExIII_27
```

Consider our standard idempotent

```savedLean
inductive X
  | x₀ | x₁

def α : X ⟶ X
    | X.x₀ => X.x₀
    | X.x₁ => X.x₀

def Xα : SetWithIdemEndomap := {
  t := X
  carrier := Set.univ
  toEnd := α
  toEnd_mem := fun _ ↦ Set.mem_univ _
  idem := by
    funext x
    cases x <;> rfl
}
```

and let $`Y^{↻\beta}` be any _automorphism_. Show that any 𝑺↻-map $`{X^{↻\alpha} \xrightarrow{f} Y^{↻\beta}}` must be non-injective, i.e. must map _both_ elements of $`X` to the _same_ (fixed) point of $`\beta` in $`Y`.
:::

:::solution (solutionTo := "Exercise 27")
We show that any 𝑺↻-map $`{X^{↻\alpha} \xrightarrow{f} Y^{↻\beta}}` must be non-injective.

```savedLean
example (Yβ : SetWithInvEndomap)
    (f : Xα.toSetWithEndomap ⟶ Yβ.toSetWithEndomap)
    : f X.x₀ = f X.x₁ := by
  obtain ⟨βinv, hβ_inv, _⟩ := Yβ.inv
  obtain ⟨f, _, hf_comm⟩ := f
  have hf_comm_x₀ : (f ⊚ Xα.toEnd) X.x₀ = (Yβ.toEnd ⊚ f) X.x₀ :=
    congrFun hf_comm X.x₀
  have hf_comm_x₁ : (f ⊚ Xα.toEnd) X.x₁ = (Yβ.toEnd ⊚ f) X.x₁ :=
    congrFun hf_comm X.x₁
  dsimp [Xα, α] at hf_comm_x₀ hf_comm_x₁
  have hβfx_eq : Yβ.toEnd (f X.x₀) = Yβ.toEnd (f X.x₁) := by
    rw [← hf_comm_x₀, hf_comm_x₁]
  have h_cancel
      : (βinv ⊚ Yβ.toEnd) (f X.x₀) = (βinv ⊚ Yβ.toEnd) (f X.x₁) :=
    congrArg βinv hβfx_eq
  rwa [hβ_inv] at h_cancel
```

```savedLean -show
end ExIII_27
```
:::

:::question (questionTitle := "Exercise 28") (questionPage := "148")
If $`X^{↻\alpha}` is any object of 𝑺↻ for which there exists an _injective_ 𝑺↻-map $`f` to some $`Y^{↻\beta}` where $`\beta` is in the subcategory of _automorphisms_, then $`\alpha` itself must be injective.
:::

:::solution (solutionTo := "Exercise 28")
```savedComment
Exercise III.28 (p. 148)
```

cf. `Mono f.val`, `Mono Xα.toEnd.val`.

```savedLean
example (Xα : SetWithEndomap) (Yβ : SetWithInvEndomap)
    (f : Xα ⟶ Yβ.toSetWithEndomap)
    (hf_inj : ∀ {U : Type} (y₁ y₂ : U ⟶ Xα.t),
        f.val ⊚ y₁ = f.val ⊚ y₂ → y₁ = y₂)
    : ∀ {T : Type} (x₁ x₂ : T ⟶ Xα.t),
        Xα.toEnd ⊚ x₁ = Xα.toEnd ⊚ x₂ → x₁ = x₂ := by
  intro _ x₁ x₂ h₁
  have h₂ : f.val ⊚ Xα.toEnd ⊚ x₁ = f.val ⊚ Xα.toEnd ⊚ x₂ := by
    congrm f.val ⊚ ?_
    exact h₁
  repeat rw [Category.assoc, f.property.2] at h₂
  obtain ⟨βinv, hβ_inv⟩ := Yβ.inv
  have h₃ : βinv ⊚ Yβ.toEnd ⊚ f.val ⊚ x₁ =
      βinv ⊚ Yβ.toEnd ⊚ f.val ⊚ x₂ := by
    congrm βinv ⊚ ?_
    exact h₂
  rw [Category.assoc, hβ_inv.1, Category.assoc (f.val ⊚ x₂),
      hβ_inv.1] at h₃
  repeat rw [Category.comp_id] at h₃
  exact hf_inj x₁ x₂ h₃
```
:::

# 11. Types of structure

:::question (questionTitle := "Exercise 29") (questionPage := "150")
Every map $`{X \xrightarrow{f} Y}` in 𝑿 gives rise to a map in the category of 𝑨-structures, by the associative law.
:::

:::solution (solutionTo := "Exercise 29")
```savedComment
Exercise III.29 (p. 150)
```

{htmlSpan (class := "todo")}[TODO Exercise III.29]
:::

:::question (questionTitle := "Exercise 30") (questionPage := "151")
If $`S`, $`s`, $`t` is a given bipointed object ... in a category 𝒞, then for each object $`X` of 𝒞, the graph of '$`X` fields' on S is actually a _reflexive_ graph, and for each map $`{X \xrightarrow{f} Y}` in 𝒞, the induced maps on sets constitute a map of reflexive graphs.
:::

:::solution (solutionTo := "Exercise 30")
```savedComment
Exercise III.30 (p. 151)
```

{htmlSpan (class := "todo")}[TODO Exercise III.30]
:::

```savedLean -show
end CM
```
