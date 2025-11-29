import VersoManual
import ConceptualMathematics.Meta.Lean
import ConceptualMathematics.Article3
import Mathlib

open Verso.Genre Manual InlineLean
open ConceptualMathematics
open CategoryTheory


#doc (Manual) "Session 11: Ascending to categories of richer structures" =>

%%%
htmlSplit := .never
number := false
%%%

```savedImport
import ConceptualMathematics.Article3
import Mathlib
open CategoryTheory
```

```savedLean -show
namespace CM
local notation:80 g " ⊚ " f:80 => CategoryStruct.comp f g
```

# 1. A category of richer structures: Endomaps of sets

:::question (questionTitle := "Exercise 1") (questionPage := "153")
How many maps can you find? (There are fewer than seven.)
:::

:::solution (solutionTo := "Exercise 1")
```savedComment
Exercise 11.1 (p. 153)
```

```savedLean -show
namespace Ex11_1
```

Label the elements in the three-element set $`A` as $`a_1`, $`a_2`, $`a_3` (clockwise starting with any element); label the elements in the set $`X` as $`x_1` for the element forming the one-element loop and $`x_2`, $`x_3`, $`x_4` (anticlockwise starting with any element) for the elements forming the three-element cycle, ignoring all other elements.

```savedLean
inductive A
  | a₁ | a₂ | a₃

inductive X
  | x₁ | x₂ | x₃ | x₄

def A' : SetWithEndomap := {
  t := A
  carrier := Set.univ
  toEnd := fun
    | A.a₁ => A.a₂
    | A.a₂ => A.a₃
    | A.a₃ => A.a₁
  toEnd_mem := fun _ ↦ Set.mem_univ _
}

def X' : SetWithEndomap := {
  t := X
  carrier := Set.univ
  toEnd := fun -- a restriction of α to the subset {x₁, x₂, x₃, x₄}
    | X.x₁ => X.x₁
    | X.x₂ => X.x₃
    | X.x₃ => X.x₄
    | X.x₄ => X.x₂
  toEnd_mem := fun _ ↦ Set.mem_univ _
}
```

Then there are four structure-preserving maps from $`A` to $`X`, which we call $`f_1`, $`f_2`, $`f_3`, $`f_4` below.

```savedLean
def f₁ : A ⟶ X
  | A.a₁ => X.x₁
  | A.a₂ => X.x₁
  | A.a₃ => X.x₁

-- f₁ is structure-preserving
example : A' ⟶ X' := ⟨
  f₁,
  by
    constructor
    · exact fun _ _ ↦ Set.mem_univ _
    · funext a
      cases a <;> rfl
⟩

def f₂ : A ⟶ X
  | A.a₁ => X.x₂
  | A.a₂ => X.x₃
  | A.a₃ => X.x₄

-- f₂ is structure-preserving
example : A' ⟶ X' := ⟨
  f₂,
  by
    constructor
    · exact fun _ _ ↦ Set.mem_univ _
    · funext a
      cases a <;> rfl
⟩

def f₃ : A ⟶ X
  | A.a₁ => X.x₃
  | A.a₂ => X.x₄
  | A.a₃ => X.x₂

-- f₃ is structure-preserving
example : A' ⟶ X' := ⟨
  f₃,
  by
    constructor
    · exact fun _ _ ↦ Set.mem_univ _
    · funext a
      cases a <;> rfl
⟩

def f₄ : A ⟶ X
  | A.a₁ => X.x₄
  | A.a₂ => X.x₂
  | A.a₃ => X.x₃

-- f₄ is structure-preserving
example : A' ⟶ X' := ⟨
  f₄,
  by
    constructor
    · exact fun _ _ ↦ Set.mem_univ _
    · funext a
      cases a <;> rfl
⟩
```

```savedLean -show
end Ex11_1
```
:::

# 3. The category of graphs

:::question (questionTitle := "Exercise 2") (questionPage := "158")
```savedComment
Exercise 11.2 (p. 158)
```

```savedLean -show
namespace Ex11_2
```

```savedLean
inductive X
  | a | b | c

def α : X ⟶ X
  | X.a => X.c
  | X.b => X.a
  | X.c => X.b

def Xα : SetWithEndomap := {
  t := X
  carrier := Set.univ
  toEnd := α
  toEnd_mem := fun _ ↦ Set.mem_univ _
}

inductive Y
  | p | q | r

def β : Y ⟶ Y
  | Y.p => Y.q
  | Y.q => Y.r
  | Y.r => Y.p

def Yβ : SetWithEndomap := {
  t := Y
  carrier := Set.univ
  toEnd := β
  toEnd_mem := fun _ ↦ Set.mem_univ _
}
```

Find an isomorphism from $`X^{↻\alpha}` to $`Y^{↻\beta}`. How many such isomorphisms are there?

Hint: You need to find $`{X \xrightarrow{f} Y}` such that $`{f \alpha = \beta f}`, and check that $`f` has an inverse $`{Y \xrightarrow{f^{-1}} X}` (meaning $`{f^{-1}f = 1_X}` and $`{ff^{-1} = 1_Y}`). Then you'll still need to check that $`f^{-1}` is a map in 𝑺↻ (meaning $`{f^{-1} \beta = \alpha f^{-1}}`), but see Exercise 4, below.
:::

:::solution (solutionTo := "Exercise 2")
There are three such isomorphisms, which we call $`f_1`, $`f_2`, $`f_3` below.

```savedLean
def f₁ : X ⟶ Y
  | X.a => Y.r
  | X.b => Y.q
  | X.c => Y.p

--f₁ is an isomorphism
example : ∃ f : Xα ⟶ Yβ, IsIso f := by
  let f : Xα ⟶ Yβ := ⟨
    f₁,
    by
      constructor
      · exact fun _ _ ↦ Set.mem_univ _
      · -- fα = βf
        funext x
        cases x <;> rfl
  ⟩
  let finv : Yβ ⟶ Xα := ⟨
    fun
      | Y.p => X.c
      | Y.q => X.b
      | Y.r => X.a,
    by
      constructor
      · exact fun _ _ ↦ Set.mem_univ _
      · -- f⁻¹β = αf⁻¹
        funext y
        cases y <;> rfl
  ⟩
  use f
  use finv
  constructor
  · -- f⁻¹f = 𝟙 X
    have h : finv.val ⊚ f.val = 𝟙 X := by
      funext x
      cases x <;> rfl
    exact Subtype.eq h
  · -- ff⁻¹ = 𝟙 Y
    have h : f.val ⊚ finv.val = 𝟙 Y := by
      funext y
      cases y <;> rfl
    exact Subtype.eq h

def f₂ : X ⟶ Y
  | X.a => Y.q
  | X.b => Y.p
  | X.c => Y.r

--f₂ is an isomorphism
example : ∃ f : Xα ⟶ Yβ, IsIso f := by
  let f : Xα ⟶ Yβ := ⟨
    f₂,
    by
      constructor
      · exact fun _ _ ↦ Set.mem_univ _
      · -- fα = βf
        funext x
        cases x <;> rfl
  ⟩
  let finv : Yβ ⟶ Xα := ⟨
    fun
      | Y.p => X.b
      | Y.q => X.a
      | Y.r => X.c,
    by
      constructor
      · exact fun _ _ ↦ Set.mem_univ _
      · -- f⁻¹β = αf⁻¹
        funext y
        cases y <;> rfl
  ⟩
  use f
  use finv
  constructor
  · -- f⁻¹f = 𝟙 X
    have h : finv.val ⊚ f.val = 𝟙 X := by
      funext x
      cases x <;> rfl
    exact Subtype.eq h
  · -- ff⁻¹ = 𝟙 Y
    have h : f.val ⊚ finv.val = 𝟙 Y := by
      funext y
      cases y <;> rfl
    exact Subtype.eq h

def f₃ : X ⟶ Y
  | X.a => Y.p
  | X.b => Y.r
  | X.c => Y.q

--f₃ is an isomorphism
example : ∃ f : Xα ⟶ Yβ, IsIso f := by
  let f : Xα ⟶ Yβ := ⟨
    f₃,
    by
      constructor
      · exact fun _ _ ↦ Set.mem_univ _
      · -- fα = βf
        funext x
        cases x <;> rfl
  ⟩
  let finv : Yβ ⟶ Xα := ⟨
    fun
      | Y.p => X.a
      | Y.q => X.c
      | Y.r => X.b,
    by
      constructor
      · exact fun _ _ ↦ Set.mem_univ _
      · -- f⁻¹β = αf⁻¹
        funext y
        cases y <;> rfl
  ⟩
  use f
  use finv
  constructor
  · -- f⁻¹f = 𝟙 X
    have h : finv.val ⊚ f.val = 𝟙 X := by
      funext x
      cases x <;> rfl
    exact Subtype.eq h
  · -- ff⁻¹ = 𝟙 Y
    have h : f.val ⊚ finv.val = 𝟙 Y := by
      funext y
      cases y <;> rfl
    exact Subtype.eq h
```

```savedLean -show
end Ex11_2
```
:::

:::question (questionTitle := "Exercise 3") (questionPage := "159")
```savedComment
Exercise 11.3 (p. 159)
```

```savedLean -show
namespace Ex11_3
```

Prove that there is no isomorphism (in 𝑺↻)

from

```savedLean
inductive X
  | x₁ | x₂ | x₃ | x₄

def α : X ⟶ X
  | X.x₁ => X.x₂
  | X.x₂ => X.x₃
  | X.x₃ => X.x₄
  | X.x₄ => X.x₂

def Xα : SetWithEndomap := {
  t := X
  carrier := Set.univ
  toEnd := α
  toEnd_mem := fun _ ↦ Set.mem_univ _
}
```

to

```savedLean
inductive Y
  | y₁ | y₂ | y₃ | y₄

def β : Y ⟶ Y
  | Y.y₁ => Y.y₂
  | Y.y₂ => Y.y₃
  | Y.y₃ => Y.y₄
  | Y.y₄ => Y.y₁

def Yβ : SetWithEndomap := {
  t := Y
  carrier := Set.univ
  toEnd := β
  toEnd_mem := fun _ ↦ Set.mem_univ _
}
```

Hint: In fact, more is true: there is no map (in 𝑺↻) from $`X^{↻\alpha}` to $`Y^{↻\beta}`.
:::

:::solution (solutionTo := "Exercise 3")
We give a proof by contradiction below.

```savedLean
example : ¬(∃ f : Xα ⟶ Yβ, IsIso f) := by
  rintro ⟨f, _⟩
  -- X.x₂ is a fixed point of α ⊚ α ⊚ α,
  have h₁ : (Xα.toEnd ⊚ Xα.toEnd ⊚ Xα.toEnd) X.x₂ = X.x₂ := by rfl
  -- but β ⊚ β ⊚ β has no fixed points in Y
  have h₂ : ∀ y : Y, (Yβ.toEnd ⊚ Yβ.toEnd ⊚ Yβ.toEnd) y ≠ y := by
    intro y
    cases y <;> exact fun h ↦ by contradiction
  -- Since f ⊚ (α ⊚ α ⊚ α) = (β ⊚ β ⊚ β) ⊚ f, we can derive a
  -- contradiction
  have h_contra : f.val ((Xα.toEnd ⊚ Xα.toEnd ⊚ Xα.toEnd) X.x₂) =
      (Yβ.toEnd ⊚ Yβ.toEnd ⊚ Yβ.toEnd) (f.val X.x₂) := by
    rw [← types_comp_apply f.val (Yβ.toEnd ⊚ Yβ.toEnd ⊚ Yβ.toEnd),
        ← Category.assoc, ← Category.assoc, ← f.property.2]
    rw [Category.assoc Xα.toEnd f.val, ← f.property.2]
    rw [Category.assoc Xα.toEnd (f.val ⊚ Xα.toEnd),
        Category.assoc Xα.toEnd f.val, ← f.property.2]
    rw [← Category.assoc, ← Category.assoc,
        types_comp_apply (Xα.toEnd ⊚ Xα.toEnd ⊚ Xα.toEnd)]
  have : (Yβ.toEnd ⊚ Yβ.toEnd ⊚ Yβ.toEnd) (f.val X.x₂) =
      f.val X.x₂ := by
    rw [← h_contra, h₁]
  have : (Yβ.toEnd ⊚ Yβ.toEnd ⊚ Yβ.toEnd) (f.val X.x₂) ≠
      f.val X.x₂ := h₂ (f.val X.x₂)
  contradiction
```

```savedLean -show
end Ex11_3
```
:::

:::question (questionTitle := "Exercise 4") (questionPage := "159")
Suppose $`{A^{↻\alpha} \xrightarrow{f} B^{↻\beta}}` is a map in 𝑺↻, and that as a map of sets, $`{A \xrightarrow{f} B}` has an inverse $`{B \xrightarrow{f^{-1}} A}`. Show that $`f^{-1}` is automatically a map in 𝑺↻.
:::

:::solution (solutionTo := "Exercise 4")
```savedComment
Exercise 11.4 (p. 159)
```

Let $`{g = f^{-1}}`.

```savedLean
example {Aα Bβ : SetWithEndomap} (f : Aα ⟶ Bβ)
    (g : Bβ.t ⟶ Aα.t) (hg_mtc : ∀ b ∈ Bβ.carrier, g b ∈ Aα.carrier)
    (h : g ⊚ f.val = 𝟙 Aα.t ∧ f.val ⊚ g = 𝟙 Bβ.t)
    : ∃ finv : Bβ ⟶ Aα, finv.val = g := by
  obtain ⟨f, _, hf_comm⟩ := f
  use ⟨
    g,
    by
      constructor
      · exact hg_mtc
      · funext b
        apply_fun f
        · rw [← types_comp_apply (g ⊚ Bβ.toEnd) f, Category.assoc,
              h.2, Category.comp_id]
          rw [← types_comp_apply (Aα.toEnd ⊚ g) f, Category.assoc,
              hf_comm, ← Category.assoc, h.2, Category.id_comp]
        · intro a₁ a₂ hf
          have hgf := congrArg g hf
          repeat rw [← types_comp_apply f g, h.1] at hgf
          exact hgf
  ⟩
```
:::

:::question (questionTitle := "Exercise 5") (questionPage := "159")
$`{\mathbb{Z} = \{\ldots, -2, -1, 0, 1, 2, 3, \ldots\}}` is the set of integers, and $`\mathbb{Z}^{↻\alpha}` and $`\mathbb{Z}^{↻\beta}` are the maps which add 2 and 3: $`{\alpha(n) = n + 2}`, $`{\beta(n) = n + 3}`. Is $`\mathbb{Z}^{↻\alpha}` isomorphic to $`\mathbb{Z}^{↻\beta}`? (If so, find an isomorphism $`{\mathbb{Z}^{↻\alpha} \xrightarrow{f} \mathbb{Z}^{↻\beta}}`; if not, explain how you know they are not isomorphic.)
:::

:::solution (solutionTo := "Exercise 5")
```savedComment
Exercise 11.5 (p. 159)
```

```savedLean -show
namespace Ex11_5
```

Define the maps $`\mathbb{Z}^{↻\alpha}` and $`\mathbb{Z}^{↻\beta}` as `SetWithEndomap` structures.

```savedLean
def α := (· + (2 : ℤ))
def β := (· + (3 : ℤ))

abbrev ℤα : SetWithEndomap := {
  t := ℤ
  carrier := Set.univ
  toEnd := α
  toEnd_mem := fun _ ↦ Set.mem_univ _
}

abbrev ℤβ : SetWithEndomap := {
  t := ℤ
  carrier := Set.univ
  toEnd := β
  toEnd_mem := fun _ ↦ Set.mem_univ _
}
```

We show that $`\mathbb{Z}^{↻\alpha}` is not isomorphic to $`\mathbb{Z}^{↻\beta}`.

```savedLean
example (f : ℤα ⟶ ℤβ) : ¬(IsIso f) := by
  -- Assume f is an isomorphism, and derive a contradiction
  by_contra hf_iso
  -- We begin by extracting the structure-preserving property of f
  have hf_comm
      : ∀ x : ℤ, (f.val ∘ ℤα.toEnd) x = (ℤβ.toEnd ∘ f.val) x := by
    intro x
    exact congrFun f.property.2 x
  -- and unfolding the definitions of α and β
  have hf_comm' : ∀ x : ℤ, f.val (x + 2) = f.val x + 3 := hf_comm
  -- The key observation: f.val(x + 2) and f.val(x) have the same
  -- remainder when divided by 3
  have hf_mod_3_eq : ∀ x : ℤ, f.val (x + 2) ≡ f.val x [ZMOD 3] := by
    intro x
    dsimp [Int.ModEq]
    rw [hf_comm' x]
    omega
  -- Hence all even numbers map to values with the same remainder mod 3
  -- as f.val(0),
  have hf_even_congr : ∀ x : ℤ, f.val (2 * x) ≡ f.val 0 [ZMOD 3] := by
    intro x
    dsimp [Int.ModEq]
    induction x with
    | zero => simp
    | succ x' ih => rw [mul_add, mul_one, hf_mod_3_eq (2 * x'), ih]
    | pred x' ih => rw [mul_sub, ← hf_mod_3_eq (2 * (-x') - 2 * 1),
        mul_one, sub_add_cancel, ih]
  -- and all odd numbers map to values with the same remainder mod 3 as
  -- f.val(1)
  have hf_odd_congr
      : ∀ x : ℤ, f.val (2 * x + 1) ≡ f.val 1 [ZMOD 3] := by
    intro x
    dsimp [Int.ModEq]
    induction x with
    | zero => simp
    | succ x' ih =>
        rw [mul_add, mul_one]
        rw [add_assoc, add_comm 2 1, ← add_assoc]
        rw [hf_mod_3_eq (2 * x' + 1), ih]
    | pred x' ih =>
        rw [mul_sub, ← hf_mod_3_eq (2 * (-x') - 2 * 1 + 1)]
        have : 2 * (-x' : ℤ) - 2 * 1 + 1 + 2 = 2 * (-x') +1 := by ring
        rw [this]
        exact ih
  -- So the image of f.val can have at most two distinct remainders
  -- mod 3
  have hf_img_set₁ : Set.range (fun x ↦ f.val x % 3) =
      {f.val 0 % 3, f.val 1 % 3} := by
    ext b
    constructor
    · rintro ⟨a, hfa⟩
      dsimp at hfa
      rw [Set.mem_insert_iff, Set.mem_singleton_iff]
      rcases Int.even_or_odd a with ha_even | ha_odd
      · left
        obtain ⟨a', ha_even⟩ := ha_even
        rw [← hfa, ha_even, ← two_mul, hf_even_congr a']
      · right
        obtain ⟨a', ha_odd⟩ := ha_odd
        rw [← hfa, ha_odd, hf_odd_congr a']
    · intro hb
      rcases hb with hb_mem | hb_mem <;> (rw [hb_mem]; simp)
  -- Now, since f is an isomorphism, f.val is bijective
  have hf_bij : Function.Bijective f.val :=
    ConcreteCategory.bijective_of_isIso f
  -- and hence surjective,
  have hf_surj : Function.Surjective f.val := hf_bij.right
  -- but a surjective function on ℤ must hit all three remainders mod 3
  have hf_img_set₂ : Set.range (fun x ↦ f.val x % 3) = {0, 1, 2} := by
    ext b
    constructor
    · rintro ⟨a, hfa⟩
      dsimp at hfa
      have hf_lbound : 0 ≤ f.val a % 3 := Int.emod_nonneg
          (f.val a) (by decide : (3 : ℤ) ≠ 0)
      have hf_ubound : f.val a % 3 < 3 := Int.emod_lt_of_pos
          (f.val a) (by decide : (0 < (3 : ℤ)))
      interval_cases k : f.val a % 3 using hf_lbound, hf_ubound <;>
        (rw [← hfa]; bound)
    · rintro (hb | hb | hb)
      all_goals
        obtain ⟨a, hfa⟩ := hf_surj b
        use a
        dsimp
        rw [hfa, hb]
        norm_num1
  -- Since we have found that the image of f.val can have at most two
  -- distinct elements and must also have exactly three distinct
  -- elements, we have a contradiction
  have h_card₁
      : Set.ncard ({f.val 0 % 3, f.val 1 % 3} : Set ℤ) ≤ 2 := by
    have h := Set.ncard_insert_le (f.val 0 % 3) {f.val 1 % 3}
    rwa [Set.ncard_singleton] at h
  have h_card₂ : Set.ncard ({0, 1, 2} : Set ℤ) = 3 := by norm_num
  rw [← hf_img_set₁, hf_img_set₂, h_card₂] at h_card₁
  linarith
```

```savedLean -show
end Ex11_5
```
:::

:::question (questionTitle := "Exercise 6") (questionPage := "159")
Each of the following graphs is isomorphic to exactly one of the others. Which?
:::

:::solution (solutionTo := "Exercise 6")
```savedComment
Exercise 11.6 (p. 159)
```

```savedLean -show
namespace Ex11_6
```

We label the arrows in each graph from top to bottom.

```savedLean
inductive A
  | a₁ | a₂ | a₃
```

We label the dots in each graph from left to right.

```savedLean
inductive D
  | d₁ | d₂ | d₃
```

Then the six graphs (a) to (f) are as follows:

```savedLean
def graph_a : IrreflexiveGraph := {
  tA := A
  carrierA := Set.univ
  tD := D
  carrierD := Set.univ
  toSrc := fun
    | A.a₁ => D.d₂
    | A.a₂ => D.d₁
    | A.a₃ => D.d₃
  toSrc_mem := fun _ ↦ Set.mem_univ _
  toTgt := fun
    | A.a₁ => D.d₃
    | A.a₂ => D.d₂
    | A.a₃ => D.d₂
  toTgt_mem := fun _ ↦ Set.mem_univ _
}

def graph_b : IrreflexiveGraph := {
  tA := A
  carrierA := Set.univ
  tD := D
  carrierD := Set.univ
  toSrc := fun
    | A.a₁ => D.d₁
    | A.a₂ => D.d₂
    | A.a₃ => D.d₂,
  toSrc_mem := fun _ ↦ Set.mem_univ _
  toTgt := fun
    | A.a₁ => D.d₂
    | A.a₂ => D.d₃
    | A.a₃ => D.d₁
  toTgt_mem := fun _ ↦ Set.mem_univ _
}

def graph_c : IrreflexiveGraph := {
  tA := A
  carrierA := Set.univ
  tD := D
  carrierD := Set.univ
  toSrc := fun
    | A.a₁ => D.d₁
    | A.a₂ => D.d₁
    | A.a₃ => D.d₁
  toSrc_mem := fun _ ↦ Set.mem_univ _
  toTgt := fun
    | A.a₁ => D.d₃
    | A.a₂ => D.d₂
    | A.a₃ => D.d₃
  toTgt_mem := fun _ ↦ Set.mem_univ _
}

def graph_d : IrreflexiveGraph := {
  tA := A
  carrierA := Set.univ
  tD := D
  carrierD := Set.univ
  toSrc := fun
    | A.a₁ => D.d₃
    | A.a₂ => D.d₁
    | A.a₃ => D.d₂
  toSrc_mem := fun _ ↦ Set.mem_univ _
  toTgt := fun
    | A.a₁ => D.d₂
    | A.a₂ => D.d₂
    | A.a₃ => D.d₃
  toTgt_mem := fun _ ↦ Set.mem_univ _
}

def graph_e : IrreflexiveGraph := {
  tA := A
  carrierA := Set.univ
  tD := D
  carrierD := Set.univ
  toSrc := fun
    | A.a₁ => D.d₁
    | A.a₂ => D.d₁
    | A.a₃ => D.d₃
  toSrc_mem := fun _ ↦ Set.mem_univ _
  toTgt := fun
    | A.a₁ => D.d₃
    | A.a₂ => D.d₂
    | A.a₃ => D.d₁
  toTgt_mem := fun _ ↦ Set.mem_univ _
}

def graph_f : IrreflexiveGraph := {
  tA := A
  carrierA := Set.univ
  tD := D
  carrierD := Set.univ
  toSrc := fun
    | A.a₁ => D.d₁
    | A.a₂ => D.d₁
    | A.a₃ => D.d₁
  toSrc_mem := fun _ ↦ Set.mem_univ _
  toTgt := fun
    | A.a₁ => D.d₂
    | A.a₂ => D.d₃
    | A.a₃ => D.d₃
  toTgt_mem := fun _ ↦ Set.mem_univ _
}
```

Graph (a) is isomorphic to graph (d).

```savedLean
def f₁ : graph_a ⟶ graph_d := {
  val := (
    fun -- maps arrows
      | A.a₁ => A.a₃
      | A.a₂ => A.a₂
      | A.a₃ => A.a₁,
    fun -- maps dots
      | D.d₁ => D.d₁
      | D.d₂ => D.d₂
      | D.d₃ => D.d₃
  )
  property := by
    split_ands
    all_goals
      first | exact fun _ _ ↦ Set.mem_univ _
            | funext x; cases x <;> rfl
}

def finv₁ : graph_d ⟶ graph_a := {
  val := (
    fun -- maps arrows
      | A.a₁ => A.a₃
      | A.a₂ => A.a₂
      | A.a₃ => A.a₁,
    fun -- maps dots
      | D.d₁ => D.d₁
      | D.d₂ => D.d₂
      | D.d₃ => D.d₃
  )
  property := by
    split_ands
    all_goals
      first | exact fun _ _ ↦ Set.mem_univ _
            | funext x; cases x <;> rfl
}

example : graph_a ≅ graph_d := {
  hom := f₁,
  inv := finv₁,
  hom_inv_id := by
    have h₁ : (finv₁.val.1 ⊚ f₁.val.1 = 𝟙 graph_a.tA) ∧
        (finv₁.val.2 ⊚ f₁.val.2 = 𝟙 graph_a.tD) := by
      constructor <;> (funext x; cases x <;> rfl)
    have h₂ : (finv₁.val.1 ⊚ f₁.val.1, finv₁.val.2 ⊚ f₁.val.2) =
        (𝟙 graph_a.tA, 𝟙 graph_a.tD) := by
      rw [h₁.1, h₁.2]
    exact Subtype.eq h₂,
  inv_hom_id := by
    have h₁ : (f₁.val.1 ⊚ finv₁.val.1 = 𝟙 graph_d.tA) ∧
        (f₁.val.2 ⊚ finv₁.val.2 = 𝟙 graph_d.tD) := by
      constructor <;> (funext x; cases x <;> rfl)
    have h₂ : (f₁.val.1 ⊚ finv₁.val.1, f₁.val.2 ⊚ finv₁.val.2) =
        (𝟙 graph_d.tA, 𝟙 graph_d.tD) := by
      rw [h₁.1, h₁.2]
    exact Subtype.eq h₂
}
```

Graph (b) is isomorphic to graph (e).

```savedLean
def f₂ : graph_b ⟶ graph_e := {
  val := (
    fun -- maps arrows
      | A.a₁ => A.a₃
      | A.a₂ => A.a₂
      | A.a₃ => A.a₁,
    fun -- maps dots
      | D.d₁ => D.d₃
      | D.d₂ => D.d₁
      | D.d₃ => D.d₂
  )
  property := by
    split_ands
    all_goals
      first | exact fun _ _ ↦ Set.mem_univ _
            | funext x; cases x <;> rfl
}

def finv₂ : graph_e ⟶ graph_b := {
  val := (
    fun -- maps arrows
      | A.a₁ => A.a₃
      | A.a₂ => A.a₂
      | A.a₃ => A.a₁,
    fun -- maps dots
      | D.d₁ => D.d₂
      | D.d₂ => D.d₃
      | D.d₃ => D.d₁
  )
  property := by
    split_ands
    all_goals
      first | exact fun _ _ ↦ Set.mem_univ _
            | funext x; cases x <;> rfl
}

example : graph_b ≅ graph_e := {
  hom := f₂,
  inv := finv₂,
  hom_inv_id := by
    have h₁ : (finv₂.val.1 ⊚ f₂.val.1 = 𝟙 graph_b.tA) ∧
        (finv₂.val.2 ⊚ f₂.val.2 = 𝟙 graph_b.tD) := by
      constructor <;> (funext x; cases x <;> rfl)
    have h₂ : (finv₂.val.1 ⊚ f₂.val.1, finv₂.val.2 ⊚ f₂.val.2) =
        (𝟙 graph_b.tA, 𝟙 graph_b.tD) := by
      rw [h₁.1, h₁.2]
    exact Subtype.eq h₂,
  inv_hom_id := by
    have h₁ : (f₂.val.1 ⊚ finv₂.val.1 = 𝟙 graph_e.tA) ∧
        (f₂.val.2 ⊚ finv₂.val.2 = 𝟙 graph_e.tD) := by
      constructor <;> (funext x; cases x <;> rfl)
    have h₂ : (f₂.val.1 ⊚ finv₂.val.1, f₂.val.2 ⊚ finv₂.val.2) =
        (𝟙 graph_e.tA, 𝟙 graph_e.tD) := by
      rw [h₁.1, h₁.2]
    exact Subtype.eq h₂
}
```

Graph (c) is isomorphic to graph (f).

```savedLean
def f₃ : graph_c ⟶ graph_f := {
  val := (
    fun -- maps arrows
      | A.a₁ => A.a₂
      | A.a₂ => A.a₁
      | A.a₃ => A.a₃,
    fun -- maps dots
      | D.d₁ => D.d₁
      | D.d₂ => D.d₂
      | D.d₃ => D.d₃
  )
  property := by
    split_ands
    all_goals
      first | exact fun _ _ ↦ Set.mem_univ _
            | funext x; cases x <;> rfl
}

def finv₃ : graph_f ⟶ graph_c := {
  val := (
    fun -- maps arrows
      | A.a₁ => A.a₂
      | A.a₂ => A.a₁
      | A.a₃ => A.a₃,
    fun -- maps dots
      | D.d₁ => D.d₁
      | D.d₂ => D.d₂
      | D.d₃ => D.d₃
  )
  property := by
    split_ands
    all_goals
      first | exact fun _ _ ↦ Set.mem_univ _
            | funext x; cases x <;> rfl
}

example : graph_c ≅ graph_f := {
  hom := f₃,
  inv := finv₃,
  hom_inv_id := by
    have h₁ : (finv₃.val.1 ⊚ f₃.val.1 = 𝟙 graph_c.tA) ∧
        (finv₃.val.2 ⊚ f₃.val.2 = 𝟙 graph_c.tD) := by
      constructor <;> (funext x; cases x <;> rfl)
    have h₂ : (finv₃.val.1 ⊚ f₃.val.1, finv₃.val.2 ⊚ f₃.val.2) =
        (𝟙 graph_c.tA, 𝟙 graph_c.tD) := by
      rw [h₁.1, h₁.2]
    exact Subtype.eq h₂,
  inv_hom_id := by
    have h₁ : (f₃.val.1 ⊚ finv₃.val.1 = 𝟙 graph_f.tA) ∧
        (f₃.val.2 ⊚ finv₃.val.2 = 𝟙 graph_f.tD) := by
      constructor <;> (funext x; cases x <;> rfl)
    have h₂ : (f₃.val.1 ⊚ finv₃.val.1, f₃.val.2 ⊚ finv₃.val.2) =
        (𝟙 graph_f.tA, 𝟙 graph_f.tD) := by
      rw [h₁.1, h₁.2]
    exact Subtype.eq h₂
}
```

```savedLean -show
end Ex11_6
```
:::

:::question (questionTitle := "Exercise 7") (questionPage := "160")
If these two graphs are isomorphic, find an isomorphism between them; if they are not isomorphic, explain how you know they are not.
:::

:::solution (solutionTo := "Exercise 7")
```savedComment
Exercise 11.7 (p. 160)
```

```savedLean -show
namespace Ex11_7
```

We label the arrows in each graph starting with the arrow at the bottom left and moving clockwise through the four outer arrows ($`a_1` to $`a_4`) and then vertically upwards through the two inner arrows ($`a_5` and $`a_6`).

```savedLean
inductive A
  | a₁ | a₂ | a₃ | a₄ | a₅ | a₆
```

We label the dots in each graph starting with the bottom dot and moving clockwise through the four outer dots ($`d_1` to $`d_4`) and then finishing with the centre dot ($`d_5`).

```savedLean
inductive D
  | d₁ | d₂ | d₃ | d₄ | d₅
```

Then the two graphs are as follows:

```savedLean
def graph_L : IrreflexiveGraph := {
  tA := A
  carrierA := Set.univ
  tD := D
  carrierD := Set.univ
  toSrc := fun
    | A.a₁ => D.d₁
    | A.a₂ => D.d₂
    | A.a₃ => D.d₃
    | A.a₄ => D.d₄
    | A.a₅ => D.d₁
    | A.a₆ => D.d₅
  toSrc_mem := fun _ ↦ Set.mem_univ _
  toTgt := fun
    | A.a₁ => D.d₂
    | A.a₂ => D.d₃
    | A.a₃ => D.d₄
    | A.a₄ => D.d₁
    | A.a₅ => D.d₅
    | A.a₆ => D.d₃
  toTgt_mem := fun _ ↦ Set.mem_univ _
}

def graph_R : IrreflexiveGraph := {
  tA := A
  carrierA := Set.univ
  tD := D
  carrierD := Set.univ
  toSrc := fun
    | A.a₁ => D.d₂
    | A.a₂ => D.d₃
    | A.a₃ => D.d₃
    | A.a₄ => D.d₄
    | A.a₅ => D.d₁
    | A.a₆ => D.d₅
  toSrc_mem := fun _ ↦ Set.mem_univ _
  toTgt := fun
    | A.a₁ => D.d₁
    | A.a₂ => D.d₂
    | A.a₃ => D.d₄
    | A.a₄ => D.d₁
    | A.a₅ => D.d₅
    | A.a₆ => D.d₃
  toTgt_mem := fun _ ↦ Set.mem_univ _
}
```

The two graphs are isomorphic, with an isomorphism between them given by $`f` below.

```savedLean
def f : graph_L ⟶ graph_R := {
  val := (
    fun -- maps arrows
      | A.a₁ => A.a₃
      | A.a₂ => A.a₄
      | A.a₃ => A.a₅
      | A.a₄ => A.a₆
      | A.a₅ => A.a₂
      | A.a₆ => A.a₁
      ,
    fun -- maps dots
      | D.d₁ => D.d₃
      | D.d₂ => D.d₄
      | D.d₃ => D.d₁
      | D.d₄ => D.d₅
      | D.d₅ => D.d₂
  )
  property := by
    split_ands
    all_goals
      first | exact fun _ _ ↦ Set.mem_univ _
            | funext x; cases x <;> rfl
}

def finv : graph_R ⟶ graph_L := {
  val := (
    fun -- maps arrows
      | A.a₁ => A.a₆
      | A.a₂ => A.a₅
      | A.a₃ => A.a₁
      | A.a₄ => A.a₂
      | A.a₅ => A.a₃
      | A.a₆ => A.a₄,
    fun -- maps dots
      | D.d₁ => D.d₃
      | D.d₂ => D.d₅
      | D.d₃ => D.d₁
      | D.d₄ => D.d₂
      | D.d₅ => D.d₄
  )
  property := by
    split_ands
    all_goals
      first | exact fun _ _ ↦ Set.mem_univ _
            | funext x; cases x <;> rfl
}

example : graph_L ≅ graph_R := {
  hom := f,
  inv := finv,
  hom_inv_id := by
    have h₁ : (finv.val.1 ⊚ f.val.1 = 𝟙 graph_L.tA) ∧
        (finv.val.2 ⊚ f.val.2 = 𝟙 graph_L.tD) := by
      constructor <;> (funext x; cases x <;> rfl)
    have h₂ : (finv.val.1 ⊚ f.val.1, finv.val.2 ⊚ f.val.2) =
        (𝟙 graph_L.tA, 𝟙 graph_L.tD) := by
      rw [h₁.1, h₁.2]
    exact Subtype.eq h₂,
  inv_hom_id := by
    have h₁ : (f.val.1 ⊚ finv.val.1 = 𝟙 graph_R.tA) ∧
        (f.val.2 ⊚ finv.val.2 = 𝟙 graph_R.tD) := by
      constructor <;> (funext x; cases x <;> rfl)
    have h₂ : (f.val.1 ⊚ finv.val.1, f.val.2 ⊚ finv.val.2) =
        (𝟙 graph_R.tA, 𝟙 graph_R.tD) := by
      rw [h₁.1, h₁.2]
    exact Subtype.eq h₂
}
```

```savedLean -show
end Ex11_7
```
:::

:::question (questionTitle := "Exercise 8") (questionPage := "160")
```savedComment
Exercise 11.8 (p. 160)
```

```savedLean -show
namespace Ex11_8
```

(Impossible journeys) $`J` is the graph

```savedLean
inductive A
  | a₁ | a₂ | a₃

abbrev D := Fin 2

def J : IrreflexiveGraph := {
  tA := A
  carrierA := Set.univ
  tD := D
  carrierD := Set.univ
  toSrc := fun
    | A.a₁ => 0
    | A.a₂ => 1
    | A.a₃ => 1
  toSrc_mem := fun _ ↦ Set.mem_univ _
  toTgt := fun
    | A.a₁ => 0
    | A.a₂ => 0
    | A.a₃ => 1
  toTgt_mem := fun _ ↦ Set.mem_univ _
}
```

$`G` is any graph, and $`b` and $`e` are dots of $`G`.

```savedLean
variable (G : IrreflexiveGraph)
         (b e : G.tD) (hb : b ∈ G.carrierD) (he : e ∈ G.carrierD)
```

\(a\) Suppose that $`{G \xrightarrow{f} J}` is a map of graphs with $`{fb = 0}` and $`{fe = 1}`. Show that there is no path in $`G` that begins at $`b` and ends at $`e`.

\(b\) Conversely, suppose that there is no path in $`G` that begins at $`b` and ends at $`e`. Show that there is a map $`{G \xrightarrow{f} J}` with $`{fb = 0}` and $`{fe = 1}`.
:::

:::solution (solutionTo := "Exercise 8")
{htmlSpan (class := "todo")}[TODO Exercise 11.8]

```savedLean -show
end Ex11_8
```
:::

```savedLean -show
end CM
```
